using J2N;
using J2N.Threading.Atomic;
using Lucene.Net.Diagnostics;
using Lucene.Net.Support;
using Lucene.Net.Support.Threading;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.IO;
using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;
using System.Text;
using System.Threading;
using JCG = J2N.Collections.Generic;
using Analyzer = Lucene.Net.Analysis.Analyzer;
using BytesRef = Lucene.Net.Util.BytesRef;
using Codec = Lucene.Net.Codecs.Codec;
using CompoundFileDirectory = Lucene.Net.Store.CompoundFileDirectory;
using Constants = Lucene.Net.Util.Constants;
using Directory = Lucene.Net.Store.Directory;
using FieldNumbers = Lucene.Net.Index.FieldInfos.FieldNumbers;
using IBits = Lucene.Net.Util.IBits;
using InfoStream = Lucene.Net.Util.InfoStream;
using IOContext = Lucene.Net.Store.IOContext;
using IOUtils = Lucene.Net.Util.IOUtils;
using Lock = Lucene.Net.Store.Lock;
using LockObtainFailedException = Lucene.Net.Store.LockObtainFailedException;
using Lucene3xCodec = Lucene.Net.Codecs.Lucene3x.Lucene3xCodec;
using Lucene3xSegmentInfoFormat = Lucene.Net.Codecs.Lucene3x.Lucene3xSegmentInfoFormat;
using MergeInfo = Lucene.Net.Store.MergeInfo;
using Query = Lucene.Net.Search.Query;
using TrackingDirectoryWrapper = Lucene.Net.Store.TrackingDirectoryWrapper;


namespace Lucene.Net.Index
{
    public class IndexWriter : IDisposable, ITwoPhaseCommit
    {
        private const int UNBOUNDED_MAX_MERGE_SEGMENTS = -1;
        public static readonly string WRITE_LOCK_NAME = "write.lock";
        public static readonly string SOURCE = "source";
        public static readonly string SOURCE_MERGE = "merge";
        public static readonly string SOURCE_FLUSH = "flush";
        public static readonly string SOURCE_ADDINDEXES_READERS = "AddIndexes(params IndexReader[] readers)";

        public static readonly int MAX_TERM_LENGTH = DocumentsWriterPerThread.MAX_TERM_LENGTH_UTF8;

        private volatile bool hitOOM;

        private readonly Directory directory; // where this index resides
        private readonly Analyzer analyzer; // how to analyze text

        private long changeCount; // increments every time a change is completed
        private long lastCommitChangeCount; // last changeCount that was committed

        private IList<SegmentCommitInfo> rollbackSegments; // list of segmentInfo we will fallback to if the commit fails

        internal volatile SegmentInfos pendingCommit; // set when a commit is pending (after prepareCommit() & before commit())
        internal long pendingCommitChangeCount;

        private ICollection<string> filesToCommit;

        internal readonly SegmentInfos segmentInfos; // the segments
        internal readonly FieldNumbers globalFieldNumberMap;

        private readonly DocumentsWriter docWriter;
        private readonly ConcurrentQueue<IEvent> eventQueue;
        internal readonly IndexFileDeleter deleter;

        private readonly IDictionary<SegmentCommitInfo, bool> segmentsToMerge = new Dictionary<SegmentCommitInfo, bool>();

        private int mergeMaxNumSegments;

        private Lock writeLock;

        private volatile bool closed;
        private volatile bool closing;

        private readonly JCG.HashSet<SegmentCommitInfo> mergingSegments = new JCG.HashSet<SegmentCommitInfo>();

        private readonly MergePolicy mergePolicy;
        private readonly IMergeScheduler mergeScheduler;
        private readonly Queue<MergePolicy.OneMerge> pendingMerges = new Queue<MergePolicy.OneMerge>();
        private readonly JCG.HashSet<MergePolicy.OneMerge> runningMerges = new JCG.HashSet<MergePolicy.OneMerge>();
        private IList<MergePolicy.OneMerge> mergeExceptions = new JCG.List<MergePolicy.OneMerge>();
        private long mergeGen;
        private bool stopMerges;

        internal readonly AtomicInt32 flushCount = new AtomicInt32();
        internal readonly AtomicInt32 flushDeletesCount = new AtomicInt32();

        internal ReaderPool readerPool;
        internal readonly BufferedUpdatesStream bufferedUpdatesStream;

        private volatile bool poolReaders;

        private readonly LiveIndexWriterConfig config;

        internal virtual DirectoryReader GetReader()
        {
            return GetReader(true);
        }

      
        public virtual DirectoryReader GetReader(bool applyAllDeletes)
        {
            EnsureOpen();

            long tStart = Time.NanoTime() / Time.MillisecondsPerNanosecond; // LUCENENET: Use NanoTime() rather than CurrentTimeMilliseconds() for more accurate/reliable results

            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "flush at getReader");
            }
            poolReaders = true;
            DirectoryReader r = null;
            DoBeforeFlush();
            bool anySegmentFlushed = false;
            bool success2 = false;
            try
            {
                UninterruptableMonitor.Enter(fullFlushLock);
                try
                {
                    bool success = false;
                    try
                    {
                        anySegmentFlushed = docWriter.FlushAllThreads(this);
                        if (!anySegmentFlushed)
                        {
                            flushCount.IncrementAndGet();
                        }
                        success = true;
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            MaybeApplyDeletes(applyAllDeletes);
                            r = StandardDirectoryReader.Open(this, segmentInfos, applyAllDeletes);
                            if (infoStream.IsEnabled("IW"))
                            {
                                infoStream.Message("IW", "return reader version=" + r.Version + " reader=" + r);
                            }
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                    catch (Exception oom) when (oom.IsOutOfMemoryError())
                    {
                        HandleOOM(oom, "GetReader");
                        return null;
                    }
                    finally
                    {
                        if (!success)
                        {
                            if (infoStream.IsEnabled("IW"))
                            {
                                infoStream.Message("IW", "hit exception during NRT reader");
                            }
                        }
                        docWriter.FinishFullFlush(success);
                        ProcessEvents(false, true);
                        DoAfterFlush();
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(fullFlushLock);
                }
                if (anySegmentFlushed)
                {
                    MaybeMerge(MergeTrigger.FULL_FLUSH, UNBOUNDED_MAX_MERGE_SEGMENTS);
                }
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "getReader took " + ((Time.NanoTime() / Time.MillisecondsPerNanosecond) - tStart) + " msec"); // LUCENENET: Use NanoTime() rather than CurrentTimeMilliseconds() for more accurate/reliable results
                }
                success2 = true;
            }
            finally
            {
                if (!success2)
                {
                    IOUtils.DisposeWhileHandlingException(r);
                }
            }
            return r;
        }

        internal class ReaderPool : IDisposable
        {
            private readonly IndexWriter outerInstance;

            public ReaderPool(IndexWriter outerInstance)
            {
                this.outerInstance = outerInstance;
            }

#if FEATURE_DICTIONARY_REMOVE_CONTINUEENUMERATION
            private readonly IDictionary<SegmentCommitInfo, ReadersAndUpdates> readerMap = new Dictionary<SegmentCommitInfo, ReadersAndUpdates>();
#else
            // LUCENENET: We use ConcurrentDictionary<TKey, TValue> because Dictionary<TKey, TValue> doesn't support
            // deletion while iterating, but ConcurrentDictionary does.
            private readonly IDictionary<SegmentCommitInfo, ReadersAndUpdates> readerMap = new ConcurrentDictionary<SegmentCommitInfo, ReadersAndUpdates>();
#endif

            // used only by asserts
            public virtual bool InfoIsLive(SegmentCommitInfo info)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    int idx = outerInstance.segmentInfos.IndexOf(info);
                    Debugging.Assert(idx != -1, "info={0} isn't live", info);
                    Debugging.Assert(outerInstance.segmentInfos[idx] == info, "info={0} doesn't match live info in segmentInfos", info);
                    return true;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            public virtual void Drop(SegmentCommitInfo info)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    if (readerMap.TryGetValue(info, out ReadersAndUpdates rld) && rld != null)
                    {
                        if (Debugging.AssertsEnabled) Debugging.Assert(info == rld.Info);
                        //        System.out.println("[" + Thread.currentThread().getName() + "] ReaderPool.drop: " + info);
                        readerMap.Remove(info);
                        rld.DropReaders();
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            public virtual bool AnyPendingDeletes()
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    foreach (ReadersAndUpdates rld in readerMap.Values)
                    {
                        if (rld.PendingDeleteCount != 0)
                        {
                            return true;
                        }
                    }

                    return false;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            public virtual void Release(ReadersAndUpdates rld)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    Release(rld, true);
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            public virtual void Release(ReadersAndUpdates rld, bool assertInfoLive)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    rld.DecRef();
                    if (Debugging.AssertsEnabled) Debugging.Assert(rld.RefCount() >= 1);

                    if (!outerInstance.poolReaders && rld.RefCount() == 1)
                    {
                        if (rld.WriteLiveDocs(outerInstance.directory))
                        {
                            if (Debugging.AssertsEnabled) Debugging.Assert(assertInfoLive == false || InfoIsLive(rld.Info));
                            outerInstance.CheckpointNoSIS();
                        }
                        rld.DropReaders();
                        readerMap.Remove(rld.Info);
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            public void Dispose()
            {
                Dispose(true);
                GC.SuppressFinalize(this);
            }

            protected virtual void Dispose(bool disposing)
            {
                if (disposing)
                {
                    DropAll(false);
                }
            }

            internal virtual void DropAll(bool doSave)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    Exception priorE = null;
                    foreach (var pair in readerMap)
                    {
                        ReadersAndUpdates rld = pair.Value;

                        try
                        {
                            if (doSave && rld.WriteLiveDocs(outerInstance.directory)) // Throws IOException
                            {
                                if (Debugging.AssertsEnabled) Debugging.Assert(InfoIsLive(rld.Info));
                                outerInstance.CheckpointNoSIS(); // Throws IOException
                            }
                        }
                        catch (Exception t) when (t.IsThrowable())
                        {
                            if (doSave)
                            {
                                throw; // LUCENENET: CA2200: Rethrow to preserve stack details (https://docs.microsoft.com/en-us/visualstudio/code-quality/ca2200-rethrow-to-preserve-stack-details)
                            }
                            else if (priorE is null)
                            {
                                priorE = t;
                            }
                        }

                        readerMap.Remove(pair.Key);
                        try
                        {
                            rld.DropReaders(); // Throws IOException
                        }
                        catch (Exception t) when (t.IsThrowable())
                        {
                            if (doSave)
                            {
                                throw; // LUCENENET: CA2200: Rethrow to preserve stack details (https://docs.microsoft.com/en-us/visualstudio/code-quality/ca2200-rethrow-to-preserve-stack-details)
                            }
                            else if (priorE is null)
                            {
                                priorE = t;
                            }
                        }
                    }
                    if (Debugging.AssertsEnabled) Debugging.Assert(readerMap.Count == 0);
                    IOUtils.ReThrow(priorE);
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            public virtual void Commit(SegmentInfos infos)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    foreach (SegmentCommitInfo info in infos.Segments)
                    {
                        if (readerMap.TryGetValue(info, out ReadersAndUpdates rld))
                        {
                            if (Debugging.AssertsEnabled) Debugging.Assert(rld.Info == info);
                            if (rld.WriteLiveDocs(outerInstance.directory))
                            {
                                if (Debugging.AssertsEnabled) Debugging.Assert(InfoIsLive(info));
                                outerInstance.CheckpointNoSIS();
                            }
                        }
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            public virtual ReadersAndUpdates Get(SegmentCommitInfo info, bool create)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    if (Debugging.AssertsEnabled) Debugging.Assert(info.Info.Dir == outerInstance.directory, "info.dir={0} vs {1}", info.Info.Dir, outerInstance.directory);

                    if (!readerMap.TryGetValue(info, out ReadersAndUpdates rld) || rld is null)
                    {
                        if (!create)
                        {
                            return null;
                        }
                        rld = new ReadersAndUpdates(outerInstance, info);
                        // Steal initial reference:
                        readerMap[info] = rld;
                    }
                    else
                    {
                        if (Debugging.AssertsEnabled && !(rld.Info == info))
                            throw AssertionError.Create(string.Format("rld.info={0} info={1} isLive?={2} vs {3}", rld.Info, info, InfoIsLive(rld.Info), InfoIsLive(info)));
                    }

                    if (create)
                    {
                        // Return ref to caller:
                        rld.IncRef();
                    }

                    if (Debugging.AssertsEnabled) Debugging.Assert(NoDups());

                    return rld;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

            /// <summary>
            /// Make sure that every segment appears only once in the
            /// pool:
            /// </summary>
            private bool NoDups()
            {
                JCG.HashSet<string> seen = new JCG.HashSet<string>();
                foreach (SegmentCommitInfo info in readerMap.Keys)
                {
                    if (Debugging.AssertsEnabled) Debugging.Assert(!seen.Contains(info.Info.Name));
                    seen.Add(info.Info.Name);
                }
                return true;
            }
        }

        /// <summary>
        /// Obtain the number of deleted docs for a pooled reader.
        /// If the reader isn't being pooled, the segmentInfo's
        /// delCount is returned.
        /// </summary>
        public virtual int NumDeletedDocs(SegmentCommitInfo info)
        {
            EnsureOpen(false);
            int delCount = info.DelCount;

            ReadersAndUpdates rld = readerPool.Get(info, false);
            if (rld != null)
            {
                delCount += rld.PendingDeleteCount;
            }
            return delCount;
        }

        protected internal void EnsureOpen(bool failIfDisposing)
        {
            if (closed || (failIfDisposing && closing))
            {
                throw AlreadyClosedException.Create(this.GetType().FullName, "this IndexWriter is disposed.");
            }
        }

        protected internal void EnsureOpen()
        {
            EnsureOpen(true);
        }

        internal readonly Codec codec; // for writing new segments

        public IndexWriter(Directory d, IndexWriterConfig conf)
        {
            readerPool = new ReaderPool(this);
            conf.SetIndexWriter(this); // prevent reuse by other instances
            config = new LiveIndexWriterConfig(conf);
            directory = d;
            analyzer = config.Analyzer;
            infoStream = config.InfoStream;
            mergePolicy = config.MergePolicy;
            mergePolicy.SetIndexWriter(this);
            mergeScheduler = config.MergeScheduler;
            codec = config.Codec;

            bufferedUpdatesStream = new BufferedUpdatesStream(infoStream);
            poolReaders = config.UseReaderPooling;

            writeLock = directory.MakeLock(WRITE_LOCK_NAME);

            if (!writeLock.Obtain(config.WriteLockTimeout)) // obtain write lock
            {
                throw new LockObtainFailedException("Index locked for write: " + writeLock);
            }

            bool success = false;
            try
            {
                OpenMode? mode = config.OpenMode;
                bool create;
                if (mode == OpenMode.CREATE)
                {
                    create = true;
                }
                else if (mode == OpenMode.APPEND)
                {
                    create = false;
                }
                else
                {
                    // CREATE_OR_APPEND - create only if an index does not exist
                    create = !DirectoryReader.IndexExists(directory);
                }

                segmentInfos = new SegmentInfos();

                bool initialIndexExists = true;

                if (create)
                {
                    try
                    {
                        segmentInfos.Read(directory);
                        segmentInfos.Clear();
                    }
                    catch (Exception e) when (e.IsIOException())
                    {
                        // Likely this means it's a fresh directory
                        initialIndexExists = false;
                    }

                    // Record that we have a change (zero out all
                    // segments) pending:
                    Changed();
                }
                else
                {
                    segmentInfos.Read(directory);

                    IndexCommit commit = config.IndexCommit;
                    if (commit != null)
                    {
                        if (commit.Directory != directory)
                        {
                            throw new ArgumentException(string.Format("IndexCommit's directory doesn't match my directory (mine: {0}, commit's: {1})", directory, commit.Directory));
                        }
                        SegmentInfos oldInfos = new SegmentInfos();
                        oldInfos.Read(directory, commit.SegmentsFileName);
                        segmentInfos.Replace(oldInfos);
                        Changed();
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "init: loaded commit \"" + commit.SegmentsFileName + "\"");
                        }
                    }
                }

                rollbackSegments = segmentInfos.CreateBackupSegmentInfos();

                // start with previous field numbers, but new FieldInfos
                globalFieldNumberMap = FieldNumberMap;
                config.FlushPolicy.Init(config);
                docWriter = new DocumentsWriter(this, config, directory);
                eventQueue = docWriter.EventQueue;

                // Default deleter (for backwards compatibility) is
                // KeepOnlyLastCommitDeleter:
                UninterruptableMonitor.Enter(this);
                try
                {
                    deleter = new IndexFileDeleter(directory, config.IndexDeletionPolicy, segmentInfos, infoStream, this, initialIndexExists);
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                if (deleter.startingCommitDeleted)
                {
                    Changed();
                }

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "init: create=" + create);
                    MessageState();
                }

                success = true;
            }
            finally
            {
                if (!success)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "init: hit exception on init; releasing write lock");
                    }
                    IOUtils.DisposeWhileHandlingException(writeLock);
                    writeLock = null;
                }
            }
        }

        private FieldNumbers FieldNumberMap
        {
            get
            {
                FieldNumbers map = new FieldNumbers();

                foreach (SegmentCommitInfo info in segmentInfos.Segments)
                {
                    foreach (FieldInfo fi in SegmentReader.ReadFieldInfos(info))
                    {
                        map.AddOrGet(fi.Name, fi.Number, fi.DocValuesType);
                    }
                }

                return map;
            }
        }

        public virtual LiveIndexWriterConfig Config
        {
            get
            {
                EnsureOpen(false);
                return config;
            }
        }

        private void MessageState()
        {
            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "\ndir=" + directory + "\n" + "index=" + SegString() + "\n" + "version=" + Constants.LUCENE_VERSION + "\n" + config.ToString());
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public void Dispose()
        {
            Dispose(disposing: true, waitForMerges: true);
            GC.SuppressFinalize(this);
        }


        [MethodImpl(MethodImplOptions.NoInlining)]
        [SuppressMessage("CodeQuality", "IDE0079:Remove unnecessary suppression", Justification = "This is a SonarCloud issue")]
        [SuppressMessage("Usage", "CA1816:Dispose methods should call SuppressFinalize", Justification = "This is Lucene's alternate path to Dispose() and we must suppress the finalizer here.")]
        [SuppressMessage("Usage", "S2953:Methods named \"Dispose\" should implement \"IDisposable.Dispose\"", Justification = "This is Lucene's alternate path to Dispose() and we must suppress the finalizer here.")]
        [SuppressMessage("Usage", "S3971:\"GC.SuppressFinalize\" should not be called", Justification = "This is Lucene's alternate path to Dispose() and we must suppress the finalizer here.")]
        public void Dispose(bool waitForMerges)
        {
            Dispose(disposing: true, waitForMerges);
            GC.SuppressFinalize(this);
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        protected virtual void Dispose(bool disposing, bool waitForMerges)
        {
            if (disposing)
            {
                Close(waitForMerges);
            }
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void Close(bool waitForMerges)
        {
            UninterruptableMonitor.Enter(commitLock);
            try
            {
                if (ShouldClose())
                {
                    if (hitOOM)
                    {
                        RollbackInternal();
                    }
                    else
                    {
                        CloseInternal(waitForMerges, true);
                        if (Debugging.AssertsEnabled) Debugging.Assert(AssertEventQueueAfterClose());
                    }
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(commitLock);
            }
        }

        private bool AssertEventQueueAfterClose()
        {
            if (eventQueue.IsEmpty)
            {
                return true;
            }
            foreach (IEvent e in eventQueue)
            {
                if (Debugging.AssertsEnabled) Debugging.Assert(e is DocumentsWriter.MergePendingEvent, "{0}", e);
            }
            return true;
        }

  
        private bool ShouldClose()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                while (true)
                {
                    if (!closed)
                    {
                        if (!closing)
                        {
                            closing = true;
                            return true;
                        }
                        else
                        {
                            DoWait();
                        }
                    }
                    else
                    {
                        return false;
                    }
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void CloseInternal(bool waitForMerges, bool doFlush)
        {
            bool interrupted = false;
            try
            {
                if (pendingCommit != null)
                {
                    throw IllegalStateException.Create("cannot close: prepareCommit was already called with no corresponding call to commit");
                }

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "now flush at close waitForMerges=" + waitForMerges);
                }

                docWriter.Dispose();

                try
                {
                    if (doFlush)
                    {
                        Flush(waitForMerges, true);
                    }
                    else
                    {
                        docWriter.Abort(this); // already closed -- never sync on IW
                    }
                }
                finally
                {
                    try
                    {

                        if (waitForMerges)
                        {
                            try
                            {
                                // Give merge scheduler last chance to run, in case
                                // any pending merges are waiting:
                                mergeScheduler.Merge(this, MergeTrigger.CLOSING, false);
                            }
                            catch (Util.ThreadInterruptedException)
                            {
                                // ignore any interruption, does not matter
                                interrupted = true;
                                if (infoStream.IsEnabled("IW"))
                                {
                                    infoStream.Message("IW", "interrupted while waiting for final merges");
                                }
                            }
                        }

                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            for (; ; )
                            {
                                try
                                {
                                    FinishMerges(waitForMerges && !interrupted);
                                    break;
                                }
                                catch (Util.ThreadInterruptedException)
                                {
                                    interrupted = true;
                                    if (infoStream.IsEnabled("IW"))
                                    {
                                        infoStream.Message("IW", "interrupted while waiting for merges to finish");
                                    }
                                }
                            }
                            stopMerges = true;
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                    finally
                    {
                        IOUtils.DisposeWhileHandlingException(mergePolicy, mergeScheduler);
                    }
                }

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "now call final commit()");
                }

                if (doFlush)
                {
                    CommitInternal();
                }
                ProcessEvents(false, true);
                UninterruptableMonitor.Enter(this);
                try
                {

                    readerPool.DropAll(true);
                    deleter.Dispose();
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "at close: " + SegString());
                }

                if (writeLock != null)
                {
                    writeLock.Dispose(); // release write lock
                    writeLock = null;
                }
                UninterruptableMonitor.Enter(this);
                try
                {
                    closed = true;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
                if (Debugging.AssertsEnabled)
                {
                    int numDeactivatedThreadStates = docWriter.perThreadPool.NumDeactivatedThreadStates();
                    Debugging.Assert(numDeactivatedThreadStates == docWriter.perThreadPool.MaxThreadStates, "{0} {1}", numDeactivatedThreadStates, docWriter.perThreadPool.MaxThreadStates);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "CloseInternal");
            }
            finally
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    closing = false;
                    UninterruptableMonitor.PulseAll(this);
                    if (!closed)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "hit exception while closing");
                        }
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
                if (interrupted)
                {
                    Thread.CurrentThread.Interrupt();
                }
            }
        }

        public virtual Directory Directory => directory;

        public virtual Analyzer Analyzer
        {
            get
            {
                EnsureOpen();
                return analyzer;
            }
        }
        public virtual int MaxDoc
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    EnsureOpen();
                    return docWriter.NumDocs + segmentInfos.TotalDocCount;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

        public virtual int NumDocs // LUCENENET NOTE: This is not a great candidate for a property, but changing because IndexReader has a property with the same name
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    EnsureOpen();
                    int count = docWriter.NumDocs;
                    foreach (SegmentCommitInfo info in segmentInfos)
                    {
                        count += info.Info.DocCount - NumDeletedDocs(info);
                    }
                    return count;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

       
        public virtual bool HasDeletions()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                EnsureOpen();
                if (bufferedUpdatesStream.Any())
                {
                    return true;
                }
                if (docWriter.AnyDeletions())
                {
                    return true;
                }
                if (readerPool.AnyPendingDeletes())
                {
                    return true;
                }
                foreach (SegmentCommitInfo info in segmentInfos.Segments)
                {
                    if (info.HasDeletions)
                    {
                        return true;
                    }
                }
                return false;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }


        public virtual void AddDocument(IEnumerable<IIndexableField> doc)
        {
            AddDocument(doc, analyzer);
        }


        public virtual void AddDocument(IEnumerable<IIndexableField> doc, Analyzer analyzer)
        {
            UpdateDocument(null, doc, analyzer);
        }

        public virtual void AddDocuments(IEnumerable<IEnumerable<IIndexableField>> docs)
        {
            AddDocuments(docs, analyzer);
        }

        public virtual void AddDocuments(IEnumerable<IEnumerable<IIndexableField>> docs, Analyzer analyzer)
        {
            UpdateDocuments(null, docs, analyzer);
        }

        public virtual void UpdateDocuments(Term delTerm, IEnumerable<IEnumerable<IIndexableField>> docs)
        {
            UpdateDocuments(delTerm, docs, analyzer);
        }

        public virtual void UpdateDocuments(Term delTerm, IEnumerable<IEnumerable<IIndexableField>> docs, Analyzer analyzer)
        {
            EnsureOpen();
            try
            {
                bool success = false;
                try
                {
                    if (docWriter.UpdateDocuments(docs, analyzer, delTerm))
                    {
                        ProcessEvents(true, false);
                    }
                    success = true;
                }
                finally
                {
                    if (!success)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "hit exception updating document");
                        }
                    }
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "UpdateDocuments");
            }
        }

        public virtual void DeleteDocuments(Term term)
        {
            EnsureOpen();
            try
            {
                if (docWriter.DeleteTerms(term))
                {
                    ProcessEvents(true, false);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "DeleteDocuments(Term)");
            }
        }

        public virtual bool TryDeleteDocument(IndexReader readerIn, int docID)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (readerIn is not AtomicReader reader)
                {
                    // Composite reader: lookup sub-reader and re-base docID:
                    IList<AtomicReaderContext> leaves = readerIn.Leaves;
                    int subIndex = ReaderUtil.SubIndex(docID, leaves);
                    reader = leaves[subIndex].AtomicReader;
                    docID -= leaves[subIndex].DocBase;
                    if (Debugging.AssertsEnabled)
                    {
                        Debugging.Assert(docID >= 0);
                        Debugging.Assert(docID < reader.MaxDoc);
                    }
                }
                // else: Reader is already atomic: use the incoming docID

                if (reader is not SegmentReader segmentReader)
                {
                    throw new ArgumentException("the reader must be a SegmentReader or composite reader containing only SegmentReaders");
                }

                SegmentCommitInfo info = segmentReader.SegmentInfo;

                // TODO: this is a slow linear search, but, number of
                // segments should be contained unless something is
                // seriously wrong w/ the index, so it should be a minor
                // cost:

                if (segmentInfos.IndexOf(info) != -1)
                {
                    ReadersAndUpdates rld = readerPool.Get(info, false);
                    if (rld != null)
                    {
                        UninterruptableMonitor.Enter(bufferedUpdatesStream);
                        try
                        {
                            rld.InitWritableLiveDocs();
                            if (rld.Delete(docID))
                            {
                                int fullDelCount = rld.Info.DelCount + rld.PendingDeleteCount;
                                if (fullDelCount == rld.Info.Info.DocCount)
                                {
                                    // If a merge has already registered for this
                                    // segment, we leave it in the readerPool; the
                                    // merge will skip merging it and will then drop
                                    // it once it's done:
                                    if (!mergingSegments.Contains(rld.Info))
                                    {
                                        segmentInfos.Remove(rld.Info);
                                        readerPool.Drop(rld.Info);
                                        Checkpoint();
                                    }
                                }

                                // Must bump changeCount so if no other changes
                                // happened, we still commit this change:
                                Changed();
                            }
                            //System.out.println("  yes " + info.info.name + " " + docID);
                            return true;
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(bufferedUpdatesStream);
                        }
                    }
                }
                return false;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        public virtual void DeleteDocuments(params Term[] terms)
        {
            EnsureOpen();
            try
            {
                if (docWriter.DeleteTerms(terms))
                {
                    ProcessEvents(true, false);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "DeleteDocuments(Term..)");
            }
        }

        public virtual void DeleteDocuments(Query query)
        {
            EnsureOpen();
            try
            {
                if (docWriter.DeleteQueries(query))
                {
                    ProcessEvents(true, false);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "DeleteDocuments(Query)");
            }
        }

   
        public virtual void DeleteDocuments(params Query[] queries)
        {
            EnsureOpen();
            try
            {
                if (docWriter.DeleteQueries(queries))
                {
                    ProcessEvents(true, false);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "DeleteDocuments(Query..)");
            }
        }

 
        public virtual void UpdateDocument(Term term, IEnumerable<IIndexableField> doc)
        {
            EnsureOpen();
            UpdateDocument(term, doc, analyzer);
        }

        public virtual void UpdateDocument(Term term, IEnumerable<IIndexableField> doc, Analyzer analyzer)
        {
            EnsureOpen();
            try
            {
                bool success = false;
                try
                {
                    if (docWriter.UpdateDocument(doc, analyzer, term))
                    {
                        ProcessEvents(true, false);
                    }
                    success = true;
                }
                finally
                {
                    if (!success)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "hit exception updating document");
                        }
                    }
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "UpdateDocument");
            }
        }

        public virtual void UpdateNumericDocValue(Term term, string field, long? value)
        {
            EnsureOpen();
            if (!globalFieldNumberMap.Contains(field, DocValuesType.NUMERIC))
            {
                throw new ArgumentException("can only update existing numeric-docvalues fields!");
            }
            try
            {
                if (docWriter.UpdateNumericDocValue(term, field, value))
                {
                    ProcessEvents(true, false);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "UpdateNumericDocValue");
            }
        }

        public virtual void UpdateBinaryDocValue(Term term, string field, BytesRef value)
        {
            EnsureOpen();
            if (!globalFieldNumberMap.Contains(field, DocValuesType.BINARY))
            {
                throw new ArgumentException("can only update existing binary-docvalues fields!");
            }
            try
            {
                if (docWriter.UpdateBinaryDocValue(term, field, value))
                {
                    ProcessEvents(true, false);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "UpdateBinaryDocValue");
            }
        }

        // for test purpose
        internal int SegmentCount
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    return segmentInfos.Count;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

        // for test purpose
        internal int NumBufferedDocuments
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    return docWriter.NumDocs;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

        // for test purpose
        internal ICollection<string> IndexFileNames
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    return segmentInfos.GetFiles(directory, true);
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

        // for test purpose
        internal int GetDocCount(int i)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (i >= 0 && i < segmentInfos.Count)
                {
                    return segmentInfos[i].Info.DocCount;
                }
                else
                {
                    return -1;
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        // for test purpose
        internal int FlushCount => flushCount;

        // for test purpose
        internal int FlushDeletesCount => flushDeletesCount;

        internal string NewSegmentName()
        {
            // Cannot synchronize on IndexWriter because that causes
            // deadlock
            UninterruptableMonitor.Enter(segmentInfos);
            try
            {
                changeCount++;
                segmentInfos.Changed();
                return "_" + SegmentInfos.SegmentNumberToString(segmentInfos.Counter++, allowLegacyNames: false); // LUCENENET specific - we had this right thru all of the betas, so don't change if the legacy feature is enabled
            }
            finally
            {
                UninterruptableMonitor.Exit(segmentInfos);
            }
        }

        internal readonly InfoStream infoStream;

        public virtual void ForceMerge(int maxNumSegments)
        {
            ForceMerge(maxNumSegments, true);
        }

        public virtual void ForceMerge(int maxNumSegments, bool doWait)
        {
            EnsureOpen();

            if (maxNumSegments < 1)
            {
                throw new ArgumentOutOfRangeException(nameof(maxNumSegments), "maxNumSegments must be >= 1; got " + maxNumSegments); // LUCENENET specific - changed from IllegalArgumentException to ArgumentOutOfRangeException (.NET convention)
            }

            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "forceMerge: index now " + SegString());
                infoStream.Message("IW", "now flush at forceMerge");
            }

            Flush(true, true);

            UninterruptableMonitor.Enter(this);
            try
            {
                ResetMergeExceptions();
                segmentsToMerge.Clear();
                foreach (SegmentCommitInfo info in segmentInfos.Segments)
                {
                    if (info != null) segmentsToMerge[info] = true;
                }
                mergeMaxNumSegments = maxNumSegments;

                // Now mark all pending & running merges for forced
                // merge:
                foreach (MergePolicy.OneMerge merge in pendingMerges)
                {
                    merge.MaxNumSegments = maxNumSegments;
                    if (merge.Info != null) segmentsToMerge[merge.Info] = true;
                }

                foreach (MergePolicy.OneMerge merge in runningMerges)
                {
                    merge.MaxNumSegments = maxNumSegments;
                    if (merge.Info != null) segmentsToMerge[merge.Info] = true;
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }

            MaybeMerge(MergeTrigger.EXPLICIT, maxNumSegments);

            if (doWait)
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    while (true)
                    {
                        if (hitOOM)
                        {
                            throw IllegalStateException.Create("this writer hit an OutOfMemoryError; cannot complete forceMerge");
                        }

                        if (mergeExceptions.Count > 0)
                        {
                            // Forward any exceptions in background merge
                            // threads to the current thread:
                            int size = mergeExceptions.Count;
                            for (int i = 0; i < size; i++)
                            {
                                MergePolicy.OneMerge merge = mergeExceptions[i];
                                if (merge.MaxNumSegments != -1)
                                {
                                    string message = "background merge hit exception: " + merge.SegString(directory);
                                    Exception t = merge.Exception;
                                    if (t != null)
                                    {
                                        //err.initCause(t);
                                        throw new IOException(message + t.ToString(), t);
                                    }
                                    //throw err;
                                    throw new IOException(message);
                                }
                            }
                        }

                        if (MaxNumSegmentsMergesPending())
                        {
                            DoWait();
                        }
                        else
                        {
                            break;
                        }
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                EnsureOpen();
            }
        }

        private bool MaxNumSegmentsMergesPending()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                foreach (MergePolicy.OneMerge merge in pendingMerges)
                {
                    if (merge.MaxNumSegments != -1)
                    {
                        return true;
                    }
                }

                foreach (MergePolicy.OneMerge merge in runningMerges)
                {
                    if (merge.MaxNumSegments != -1)
                    {
                        return true;
                    }
                }

                return false;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        public virtual void ForceMergeDeletes(bool doWait)
        {
            EnsureOpen();

            Flush(true, true);

            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "forceMergeDeletes: index now " + SegString());
            }

            MergePolicy.MergeSpecification spec;
            bool newMergesFound = false;

            UninterruptableMonitor.Enter(this);
            try
            {
                spec = mergePolicy.FindForcedDeletesMerges(segmentInfos);
                newMergesFound = spec != null;
                if (newMergesFound)
                {
                    int numMerges = spec.Merges.Count;
                    for (int i = 0; i < numMerges; i++)
                    {
                        RegisterMerge(spec.Merges[i]);
                    }
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }

            mergeScheduler.Merge(this, MergeTrigger.EXPLICIT, newMergesFound);

            if (spec != null && doWait)
            {
                int numMerges = spec.Merges.Count;
                UninterruptableMonitor.Enter(this);
                try
                {
                    bool running = true;
                    while (running)
                    {
                        if (hitOOM)
                        {
                            throw IllegalStateException.Create("this writer hit an OutOfMemoryError; cannot complete forceMergeDeletes");
                        }

                        running = false;
                        for (int i = 0; i < numMerges; i++)
                        {
                            MergePolicy.OneMerge merge = spec.Merges[i];
                            if (pendingMerges.Contains(merge) || runningMerges.Contains(merge))
                            {
                                running = true;
                            }
                            Exception t = merge.Exception;
                            if (t != null)
                            {
                                throw new IOException("background merge hit exception: " + merge.SegString(directory), t);
                            }
                        }

                        // If any of our merges are still running, wait:
                        if (running)
                        {
                            DoWait();
                        }
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }

        }

        public virtual void ForceMergeDeletes()
        {
            ForceMergeDeletes(true);
        }

        public void MaybeMerge()
        {
            MaybeMerge(MergeTrigger.EXPLICIT, UNBOUNDED_MAX_MERGE_SEGMENTS);
        }

        private void MaybeMerge(MergeTrigger trigger, int maxNumSegments)
        {
            EnsureOpen(false);
            bool newMergesFound = UpdatePendingMerges(trigger, maxNumSegments);
            mergeScheduler.Merge(this, trigger, newMergesFound);
        }

        private bool UpdatePendingMerges(MergeTrigger trigger, int maxNumSegments)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (Debugging.AssertsEnabled) Debugging.Assert(maxNumSegments == -1 || maxNumSegments > 0);
                //if (Debugging.AssertsEnabled) Debugging.Assert(trigger != null); // LUCENENET NOTE: Enum cannot be null in .NET
                if (stopMerges)
                {
                    return false;
                }

                // Do not start new merges if we've hit OOME
                if (hitOOM)
                {
                    return false;
                }
                bool newMergesFound; // LUCENENET specific - removed unnecessary assignment
                MergePolicy.MergeSpecification spec;
                if (maxNumSegments != UNBOUNDED_MAX_MERGE_SEGMENTS)
                {
                    if (Debugging.AssertsEnabled) Debugging.Assert(trigger == MergeTrigger.EXPLICIT || trigger == MergeTrigger.MERGE_FINISHED, "Expected EXPLICT or MERGE_FINISHED as trigger even with maxNumSegments set but was: {0}", trigger);
                    spec = mergePolicy.FindForcedMerges(segmentInfos, maxNumSegments, segmentsToMerge);
                    newMergesFound = spec != null;
                    if (newMergesFound)
                    {
                        int numMerges = spec.Merges.Count;
                        for (int i = 0; i < numMerges; i++)
                        {
                            MergePolicy.OneMerge merge = spec.Merges[i];
                            merge.MaxNumSegments = maxNumSegments;
                        }
                    }
                }
                else
                {
                    spec = mergePolicy.FindMerges(trigger, segmentInfos);
                }
                newMergesFound = spec != null;
                if (newMergesFound)
                {
                    int numMerges = spec.Merges.Count;
                    for (int i = 0; i < numMerges; i++)
                    {
                        RegisterMerge(spec.Merges[i]);
                    }
                }
                return newMergesFound;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        public virtual ICollection<SegmentCommitInfo> MergingSegments
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    return mergingSegments;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

        public virtual MergePolicy.OneMerge NextMerge()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (pendingMerges.Count == 0)
                {
                    return null;
                }
                else
                {
                    // Advance the merge from pending to running
                    MergePolicy.OneMerge merge = pendingMerges.Dequeue();
                    runningMerges.Add(merge);
                    return merge;
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        public virtual bool HasPendingMerges()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                return pendingMerges.Count != 0;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        public virtual void Rollback()
        {
            UninterruptableMonitor.Enter(commitLock);
            try
            {
                if (ShouldClose())
                {
                    RollbackInternal();
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(commitLock);
            }
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private void RollbackInternal()
        {
            bool success = false;

            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "rollback");
            }

            try
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    FinishMerges(false);
                    stopMerges = true;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "rollback: done finish merges");
                }

                mergePolicy.Dispose();
                mergeScheduler.Dispose();

                bufferedUpdatesStream.Clear();
                docWriter.Dispose(); // mark it as closed first to prevent subsequent indexing actions/flushes
                docWriter.Abort(this); // don't sync on IW here
                UninterruptableMonitor.Enter(this);
                try
                {
                    if (pendingCommit != null)
                    {
                        pendingCommit.RollbackCommit(directory);
                        deleter.DecRef(pendingCommit);
                        pendingCommit = null;
                        UninterruptableMonitor.PulseAll(this);
                    }

                    // Don't bother saving any changes in our segmentInfos
                    readerPool.DropAll(false);

           
                    segmentInfos.RollbackSegmentInfos(rollbackSegments);
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "rollback: infos=" + SegString(segmentInfos.Segments));
                    }

                    if (Debugging.AssertsEnabled) Debugging.Assert(TestPoint("rollback before checkpoint"));

                    // Ask deleter to locate unreferenced files & remove
                    // them:
                    deleter.Checkpoint(segmentInfos, false);
                    deleter.Refresh();

                    lastCommitChangeCount = changeCount;

                    deleter.Refresh();
                    deleter.Dispose();

                    IOUtils.Dispose(writeLock); // release write lock
                    writeLock = null;

                    if (Debugging.AssertsEnabled)
                    {
                        // LUCENENET specific - store the number of states so we don't have to call this method twice
                        int numDeactivatedThreadStates = docWriter.perThreadPool.NumDeactivatedThreadStates();
                        Debugging.Assert(numDeactivatedThreadStates == docWriter.perThreadPool.MaxThreadStates, "{0} {1}", numDeactivatedThreadStates, docWriter.perThreadPool.MaxThreadStates);
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                success = true;
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "RollbackInternal");
            }
            finally
            {
                if (!success)
                {
                    // Must not hold IW's lock while closing
                    // mergePolicy/Scheduler: this can lead to deadlock,
                    // e.g. TestIW.testThreadInterruptDeadlock
                    IOUtils.DisposeWhileHandlingException(mergePolicy, mergeScheduler);
                }
                UninterruptableMonitor.Enter(this);
                try
                {
                    if (!success)
                    {
                        // we tried to be nice about it: do the minimum

                        // don't leak a segments_N file if there is a pending commit
                        if (pendingCommit != null)
                        {
                            try
                            {
                                pendingCommit.RollbackCommit(directory);
                                deleter.DecRef(pendingCommit);
                            }
                            catch (Exception t) when (t.IsThrowable())
                            {
                            }
                        }

                        // close all the closeables we can (but important is readerPool and writeLock to prevent leaks)
                        IOUtils.DisposeWhileHandlingException(readerPool, deleter, writeLock);
                        writeLock = null;
                    }
                    closed = true;
                    closing = false;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

 
        public virtual void DeleteAll()
        {
            EnsureOpen();
            bool success = false;

            UninterruptableMonitor.Enter(fullFlushLock);
            try
            {
                try
                {
                    docWriter.LockAndAbortAll(this);
                    ProcessEvents(false, true);
                    UninterruptableMonitor.Enter(this);
                    try
                    {
                        try
                        {
                            // Abort any running merges
                            FinishMerges(false);
                            // Remove all segments
                            segmentInfos.Clear();
                            // Ask deleter to locate unreferenced files & remove them:
                            deleter.Checkpoint(segmentInfos, false);

                            readerPool.DropAll(false);
                            // Mark that the index has changed
                            ++changeCount;
                            segmentInfos.Changed();
                            globalFieldNumberMap.Clear();
                            success = true;
                        }
                        catch (Exception oom) when (oom.IsOutOfMemoryError())
                        {
                            HandleOOM(oom, "DeleteAll");
                        }
                        finally
                        {
                            if (!success)
                            {
                                if (infoStream.IsEnabled("IW"))
                                {
                                    infoStream.Message("IW", "hit exception during deleteAll");
                                }
                            }
                        }
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(this);
                    }
                }
                finally
                {
                    docWriter.UnlockAllAfterAbortAll(this);
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(fullFlushLock);
            }
        }

        private void FinishMerges(bool waitForMerges)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (!waitForMerges)
                {
                    stopMerges = true;

                    // Abort all pending & running merges:
                    foreach (MergePolicy.OneMerge merge in pendingMerges)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "now abort pending merge " + SegString(merge.Segments));
                        }
                        merge.Abort();
                        MergeFinish(merge);
                    }
                    pendingMerges.Clear();

                    foreach (MergePolicy.OneMerge merge in runningMerges)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "now abort running merge " + SegString(merge.Segments));
                        }
                        merge.Abort();
                    }

                    // These merges periodically check whether they have
                    // been aborted, and stop if so.  We wait here to make
                    // sure they all stop.  It should not take very long
                    // because the merge threads periodically check if
                    // they are aborted.
                    while (runningMerges.Count > 0)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "now wait for " + runningMerges.Count + " running merge/s to abort");
                        }
                        DoWait();
                    }

                    stopMerges = false;
                    UninterruptableMonitor.PulseAll(this);

                    if (Debugging.AssertsEnabled) Debugging.Assert(0 == mergingSegments.Count);

                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "all running merges have aborted");
                    }
                }
                else
                {
                    // waitForMerges() will ensure any running addIndexes finishes.
                    // It's fine if a new one attempts to start because from our
                    // caller above the call will see that we are in the
                    // process of closing, and will throw an
                    // ObjectDisposedException.
                    WaitForMerges();
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Wait for any currently outstanding merges to finish.
        ///
        /// <para>It is guaranteed that any merges started prior to calling this method
        ///    will have completed once this method completes.</para>
        /// </summary>
        public virtual void WaitForMerges()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                EnsureOpen(false);
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "waitForMerges");
                }
                while (pendingMerges.Count > 0 || runningMerges.Count > 0)
                {
                    DoWait();
                }

                // sanity check
                if (Debugging.AssertsEnabled) Debugging.Assert(0 == mergingSegments.Count);

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "waitForMerges done");
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Called whenever the <see cref="SegmentInfos"/> has been updated and
        /// the index files referenced exist (correctly) in the
        /// index directory.
        /// </summary>
        internal virtual void Checkpoint()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                Changed();
                deleter.Checkpoint(segmentInfos, false);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Checkpoints with <see cref="IndexFileDeleter"/>, so it's aware of
        /// new files, and increments <see cref="changeCount"/>, so on
        /// close/commit we will write a new segments file, but
        /// does NOT bump segmentInfos.version.
        /// </summary>
        internal virtual void CheckpointNoSIS()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                changeCount++;
                deleter.Checkpoint(segmentInfos, false);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Called internally if any index state has changed. </summary>
        internal void Changed()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                changeCount++;
                segmentInfos.Changed();
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        internal virtual void PublishFrozenUpdates(FrozenBufferedUpdates packet)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (Debugging.AssertsEnabled) Debugging.Assert(packet != null && packet.Any());
                UninterruptableMonitor.Enter(bufferedUpdatesStream);
                try
                {
                    bufferedUpdatesStream.Push(packet);
                }
                finally
                {
                    UninterruptableMonitor.Exit(bufferedUpdatesStream);
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Atomically adds the segment private delete packet and publishes the flushed
        /// segments <see cref="SegmentInfo"/> to the index writer.
        /// </summary>
        internal virtual void PublishFlushedSegment(SegmentCommitInfo newSegment, FrozenBufferedUpdates packet, FrozenBufferedUpdates globalPacket)
        {
            try
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    // Lock order IW -> BDS
                    UninterruptableMonitor.Enter(bufferedUpdatesStream);
                    try
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "publishFlushedSegment");
                        }

                        if (globalPacket != null && globalPacket.Any())
                        {
                            bufferedUpdatesStream.Push(globalPacket);
                        }
                        // Publishing the segment must be synched on IW -> BDS to make the sure
                        // that no merge prunes away the seg. private delete packet
                        long nextGen;
                        if (packet != null && packet.Any())
                        {
                            nextGen = bufferedUpdatesStream.Push(packet);
                        }
                        else
                        {
                            // Since we don't have a delete packet to apply we can get a new
                            // generation right away
                            nextGen = bufferedUpdatesStream.GetNextGen();
                        }
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "publish sets newSegment delGen=" + nextGen + " seg=" + SegString(newSegment));
                        }
                        newSegment.SetBufferedDeletesGen(nextGen);
                        segmentInfos.Add(newSegment);
                        Checkpoint();
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(bufferedUpdatesStream);
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
            finally
            {
                flushCount.IncrementAndGet();
                DoAfterFlush();
            }
        }

        private void ResetMergeExceptions()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                mergeExceptions = new JCG.List<MergePolicy.OneMerge>();
                mergeGen++;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void NoDupDirs(params Directory[] dirs)
        {
            JCG.HashSet<Directory> dups = new JCG.HashSet<Directory>();
            for (int i = 0; i < dirs.Length; i++)
            {
                if (dups.Contains(dirs[i]))
                {
                    throw new ArgumentException("Directory " + dirs[i] + " appears more than once");
                }
                if (dirs[i] == directory)
                {
                    throw new ArgumentException("Cannot add directory to itself");
                }
                dups.Add(dirs[i]);
            }
        }

        /// <summary>
        /// Acquires write locks on all the directories; be sure
        /// to match with a call to <see cref="IOUtils.Dispose(IEnumerable{IDisposable})"/> in a
        /// finally clause.
        /// </summary>
        private IEnumerable<Lock> AcquireWriteLocks(params Directory[] dirs)
        {
            IList<Lock> locks = new JCG.List<Lock>();
            for (int i = 0; i < dirs.Length; i++)
            {
                bool success = false;
                try
                {
                    Lock @lock = dirs[i].MakeLock(WRITE_LOCK_NAME);
                    locks.Add(@lock);
                    @lock.Obtain(config.WriteLockTimeout);
                    success = true;
                }
                finally
                {
                    if (!success)
                    {
                        // Release all previously acquired locks:
                        IOUtils.DisposeWhileHandlingException(locks);
                    }
                }
            }
            return locks;
        }

 
        public virtual void AddIndexes(params Directory[] dirs)
        {
            EnsureOpen();

            NoDupDirs(dirs);

            IEnumerable<Lock> locks = AcquireWriteLocks(dirs);

            bool successTop = false;

            try
            {
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "flush at addIndexes(Directory...)");
                }

                Flush(false, true);

                IList<SegmentCommitInfo> infos = new JCG.List<SegmentCommitInfo>();
                bool success = false;
                try
                {
                    foreach (Directory dir in dirs)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "addIndexes: process directory " + dir);
                        }
                        SegmentInfos sis = new SegmentInfos(); // read infos from dir
                        sis.Read(dir);
                        JCG.HashSet<string> dsFilesCopied = new JCG.HashSet<string>();
                        IDictionary<string, string> dsNames = new Dictionary<string, string>();
                        JCG.HashSet<string> copiedFiles = new JCG.HashSet<string>();
                        foreach (SegmentCommitInfo info in sis.Segments)
                        {
                            if (Debugging.AssertsEnabled) Debugging.Assert(!infos.Contains(info),"dup info dir={0} name={1}", info.Info.Dir, info.Info.Name);

                            string newSegName = NewSegmentName();

                            if (infoStream.IsEnabled("IW"))
                            {
                                infoStream.Message("IW", "addIndexes: process segment origName=" + info.Info.Name + " newName=" + newSegName + " info=" + info);
                            }

                            IOContext context = new IOContext(new MergeInfo(info.Info.DocCount, info.GetSizeInBytes(), true, -1));

                            foreach (FieldInfo fi in SegmentReader.ReadFieldInfos(info))
                            {
                                globalFieldNumberMap.AddOrGet(fi.Name, fi.Number, fi.DocValuesType);
                            }
                            infos.Add(CopySegmentAsIs(info, newSegName, dsNames, dsFilesCopied, context, copiedFiles));
                        }
                    }
                    success = true;
                }
                finally
                {
                    if (!success)
                    {
                        foreach (SegmentCommitInfo sipc in infos)
                        {
                            foreach (string file in sipc.GetFiles())
                            {
                                try
                                {
                                    directory.DeleteFile(file);
                                }
                                catch (Exception t) when (t.IsThrowable())
                                {
                                }
                            }
                        }
                    }
                }

                UninterruptableMonitor.Enter(this);
                try
                {
                    success = false;
                    try
                    {
                        EnsureOpen();
                        success = true;
                    }
                    finally
                    {
                        if (!success)
                        {
                            foreach (SegmentCommitInfo sipc in infos)
                            {
                                foreach (string file in sipc.GetFiles())
                                {
                                    try
                                    {
                                        directory.DeleteFile(file);
                                    }
                                    catch (Exception t) when (t.IsThrowable())
                                    {
                                    }
                                }
                            }
                        }
                    }
                    segmentInfos.AddAll(infos);
                    Checkpoint();
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                successTop = true;
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "AddIndexes(Directory...)");
            }
            finally
            {
                if (successTop)
                {
                    IOUtils.Dispose(locks);
                }
                else
                {
                    IOUtils.DisposeWhileHandlingException(locks);
                }
            }
        }

        public virtual void AddIndexes(params IndexReader[] readers)
        {
            EnsureOpen();
            int numDocs = 0;

            try
            {
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "flush at addIndexes(IndexReader...)");
                }
                Flush(false, true);

                string mergedName = NewSegmentName();
                IList<AtomicReader> mergeReaders = new JCG.List<AtomicReader>();
                foreach (IndexReader indexReader in readers)
                {
                    numDocs += indexReader.NumDocs;
                    foreach (AtomicReaderContext ctx in indexReader.Leaves)
                    {
                        mergeReaders.Add(ctx.AtomicReader);
                    }
                }

                IOContext context = new IOContext(new MergeInfo(numDocs, -1, true, -1));

                // TODO: somehow we should fix this merge so it's
                // abortable so that IW.close(false) is able to stop it
                TrackingDirectoryWrapper trackingDir = new TrackingDirectoryWrapper(directory);

                SegmentInfo info = new SegmentInfo(directory, Constants.LUCENE_MAIN_VERSION, mergedName, -1, false, codec, null);

                SegmentMerger merger = new SegmentMerger(mergeReaders, info, infoStream, trackingDir, config.TermIndexInterval, CheckAbort.NONE, globalFieldNumberMap, context, config.CheckIntegrityAtMerge);

                if (!merger.ShouldMerge)
                {
                    return;
                }

                MergeState mergeState;
                bool success = false;
                try
                {
                    mergeState = merger.Merge(); // merge 'em
                    success = true;
                }
                finally
                {
                    if (!success)
                    {
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            deleter.Refresh(info.Name);
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                }

                SegmentCommitInfo infoPerCommit = new SegmentCommitInfo(info, 0, -1L, -1L);

                info.SetFiles(new JCG.HashSet<string>(trackingDir.CreatedFiles));
                trackingDir.CreatedFiles.Clear();

                SetDiagnostics(info, SOURCE_ADDINDEXES_READERS);

                bool useCompoundFile;
                UninterruptableMonitor.Enter(this); // Guard segmentInfos
                try
                {
                    if (stopMerges)
                    {
                        deleter.DeleteNewFiles(infoPerCommit.GetFiles());
                        return;
                    }
                    EnsureOpen();
                    useCompoundFile = mergePolicy.UseCompoundFile(segmentInfos, infoPerCommit);
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                // Now create the compound file if needed
                if (useCompoundFile)
                {
                    ICollection<string> filesToDelete = infoPerCommit.GetFiles();
                    try
                    {
                        CreateCompoundFile(infoStream, directory, CheckAbort.NONE, info, context);
                    }
                    finally
                    {
                        // delete new non cfs files directly: they were never
                        // registered with IFD
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            deleter.DeleteNewFiles(filesToDelete);
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                    info.UseCompoundFile = true;
                }

                // Have codec write SegmentInfo.  Must do this after
                // creating CFS so that 1) .si isn't slurped into CFS,
                // and 2) .si reflects useCompoundFile=true change
                // above:
                success = false;
                try
                {
                    codec.SegmentInfoFormat.SegmentInfoWriter.Write(trackingDir, info, mergeState.FieldInfos, context);
                    success = true;
                }
                finally
                {
                    if (!success)
                    {
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            deleter.Refresh(info.Name);
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                }

                info.AddFiles(trackingDir.CreatedFiles);

                // Register the new segment
                UninterruptableMonitor.Enter(this);
                try
                {
                    if (stopMerges)
                    {
                        deleter.DeleteNewFiles(info.GetFiles());
                        return;
                    }
                    EnsureOpen();
                    segmentInfos.Add(infoPerCommit);
                    Checkpoint();
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "AddIndexes(IndexReader...)");
            }
        }

        /// <summary>
        /// Copies the segment files as-is into the <see cref="IndexWriter"/>'s directory. </summary>
        private SegmentCommitInfo CopySegmentAsIs(SegmentCommitInfo info, string segName, IDictionary<string, string> dsNames, ISet<string> dsFilesCopied, IOContext context, ISet<string> copiedFiles)
        {
            // Determine if the doc store of this segment needs to be copied. It's
            // only relevant for segments that share doc store with others,
            // because the DS might have been copied already, in which case we
            // just want to update the DS name of this SegmentInfo.
            string dsName = Lucene3xSegmentInfoFormat.GetDocStoreSegment(info.Info);
            if (Debugging.AssertsEnabled) Debugging.Assert(dsName != null);
            // LUCENENET: Eliminated extra lookup by using TryGetValue instead of ContainsKey
            if (!dsNames.TryGetValue(dsName, out string newDsName))
            {
                dsNames[dsName] = segName;
                newDsName = segName;
            }

            // note: we don't really need this fis (its copied), but we load it up
            // so we don't pass a null value to the si writer
            FieldInfos fis = SegmentReader.ReadFieldInfos(info);

            ISet<string> docStoreFiles3xOnly = Lucene3xCodec.GetDocStoreFiles(info.Info);

            IDictionary<string, string> attributes;
            // copy the attributes map, we might modify it below.
            // also we need to ensure its read-write, since we will invoke the SIwriter (which might want to set something).
#pragma warning disable CS0618 // Type or member is obsolete
            if (info.Info.Attributes is null)
            {
                attributes = new Dictionary<string, string>();
            }
            else
            {
                attributes = new Dictionary<string, string>(info.Info.Attributes);
            }
#pragma warning restore CS0618 // Type or member is obsolete
            if (docStoreFiles3xOnly != null)
            {
                // only violate the codec this way if it's preflex &
                // shares doc stores
                // change docStoreSegment to newDsName
                attributes[Lucene3xSegmentInfoFormat.DS_NAME_KEY] = newDsName;
            }

            //System.out.println("copy seg=" + info.info.name + " version=" + info.info.getVersion());
            // Same SI as before but we change directory, name and docStoreSegment:
            SegmentInfo newInfo = new SegmentInfo(directory, info.Info.Version, segName, info.Info.DocCount, info.Info.UseCompoundFile, info.Info.Codec, info.Info.Diagnostics, attributes);
            SegmentCommitInfo newInfoPerCommit = new SegmentCommitInfo(newInfo, info.DelCount, info.DelGen, info.FieldInfosGen);

            JCG.HashSet<string> segFiles = new JCG.HashSet<string>();

            // Build up new segment's file names.  Must do this
            // before writing SegmentInfo:
            foreach (string file in info.GetFiles())
            {
                string newFileName;
                if (docStoreFiles3xOnly != null && docStoreFiles3xOnly.Contains(file))
                {
                    newFileName = newDsName + Lucene.Net.Index.IndexFileNames.StripSegmentName(file);
                }
                else
                {
                    newFileName = segName + Lucene.Net.Index.IndexFileNames.StripSegmentName(file);
                }
                segFiles.Add(newFileName);
            }
            newInfo.SetFiles(segFiles);

            // We must rewrite the SI file because it references
            // segment name (its own name, if its 3.x, and doc
            // store segment name):
            TrackingDirectoryWrapper trackingDir = new TrackingDirectoryWrapper(directory);
            Codec currentCodec = newInfo.Codec;
            try
            {
                currentCodec.SegmentInfoFormat.SegmentInfoWriter.Write(trackingDir, newInfo, fis, context);
            }
            catch (Exception uoe) when (uoe.IsUnsupportedOperationException())
            {
#pragma warning disable CS0618 // Type or member is obsolete
                if (currentCodec is Lucene3xCodec)
#pragma warning restore CS0618 // Type or member is obsolete
                {
                    // OK: 3x codec cannot write a new SI file;
                    // SegmentInfos will write this on commit
                }
                else
                {
                    throw; // LUCENENET: CA2200: Rethrow to preserve stack details (https://docs.microsoft.com/en-us/visualstudio/code-quality/ca2200-rethrow-to-preserve-stack-details)
                }
            }

            ICollection<string> siFiles = trackingDir.CreatedFiles;

            bool success = false;
            try
            {
                // Copy the segment's files
                foreach (string file in info.GetFiles())
                {
                    string newFileName;
                    if (docStoreFiles3xOnly != null && docStoreFiles3xOnly.Contains(file))
                    {
                        newFileName = newDsName + Lucene.Net.Index.IndexFileNames.StripSegmentName(file);
                        if (dsFilesCopied.Contains(newFileName))
                        {
                            continue;
                        }
                        dsFilesCopied.Add(newFileName);
                    }
                    else
                    {
                        newFileName = segName + Lucene.Net.Index.IndexFileNames.StripSegmentName(file);
                    }

                    if (siFiles.Contains(newFileName))
                    {
                        // We already rewrote this above
                        continue;
                    }

                    if (Debugging.AssertsEnabled)
                    {
                        Debugging.Assert(!SlowFileExists(directory, newFileName), "file \"{0}\" already exists; siFiles={1}", newFileName, siFiles);
                        Debugging.Assert(!copiedFiles.Contains(file), "file \"{0}\" is being copied more than once", file);
                    }
                    copiedFiles.Add(file);
                    info.Info.Dir.Copy(directory, file, newFileName, context);
                }
                success = true;
            }
            finally
            {
                if (!success)
                {
                    foreach (string file in newInfo.GetFiles())
                    {
                        try
                        {
                            directory.DeleteFile(file);
                        }
                        catch (Exception t) when (t.IsThrowable())
                        {
                        }
                    }
                }
            }

            return newInfoPerCommit;
        }


        protected virtual void DoAfterFlush()
        {
        }

        protected virtual void DoBeforeFlush()
        {
        }

        public void PrepareCommit()
        {
            EnsureOpen();
            PrepareCommitInternal();
        }

        private void PrepareCommitInternal()
        {
            UninterruptableMonitor.Enter(commitLock);
            try
            {
                EnsureOpen(false);
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "prepareCommit: flush");
                    infoStream.Message("IW", "  index before flush " + SegString());
                }

                if (hitOOM)
                {
                    throw IllegalStateException.Create("this writer hit an OutOfMemoryError; cannot commit");
                }

                if (pendingCommit != null)
                {
                    throw IllegalStateException.Create("prepareCommit was already called with no corresponding call to commit");
                }

                DoBeforeFlush();
                // LUCENENET: .NET doesn't support asserts in release mode
                if (Lucene.Net.Diagnostics.Debugging.AssertsEnabled) TestPoint("startDoFlush");
                SegmentInfos toCommit = null;
                bool anySegmentsFlushed = false;


                try
                {
                    UninterruptableMonitor.Enter(fullFlushLock);
                    try
                    {
                        bool flushSuccess = false;
                        bool success = false;
                        try
                        {
                            anySegmentsFlushed = docWriter.FlushAllThreads(this);
                            if (!anySegmentsFlushed)
                            {
                                flushCount.IncrementAndGet();
                            }
                            ProcessEvents(false, true);
                            flushSuccess = true;

                            UninterruptableMonitor.Enter(this);
                            try
                            {
                                MaybeApplyDeletes(true);

                                readerPool.Commit(segmentInfos);
                                toCommit = (SegmentInfos)segmentInfos.Clone();

                                pendingCommitChangeCount = changeCount;

                                filesToCommit = toCommit.GetFiles(directory, false);
                                deleter.IncRef(filesToCommit);
                            }
                            finally
                            {
                                UninterruptableMonitor.Exit(this);
                            }
                            success = true;
                        }
                        finally
                        {
                            if (!success)
                            {
                                if (infoStream.IsEnabled("IW"))
                                {
                                    infoStream.Message("IW", "hit exception during prepareCommit");
                                }
                            }
                            // Done: finish the full flush!
                            docWriter.FinishFullFlush(flushSuccess);
                            DoAfterFlush();
                        }
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(fullFlushLock);
                    }
                }
                catch (Exception oom) when (oom.IsOutOfMemoryError())
                {
                    HandleOOM(oom, "PrepareCommit");
                }

                bool success_ = false;
                try
                {
                    if (anySegmentsFlushed)
                    {
                        MaybeMerge(MergeTrigger.FULL_FLUSH, UNBOUNDED_MAX_MERGE_SEGMENTS);
                    }
                    StartCommit(toCommit);
                    success_ = true;
                }
                finally
                {
                    if (!success_)
                    {
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            if (filesToCommit != null)
                            {
                                deleter.DecRef(filesToCommit);
                                filesToCommit = null;
                            }
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(commitLock);
            }
        }

    
        public void SetCommitData(IDictionary<string, string> commitUserData)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                segmentInfos.UserData = new Dictionary<string, string>(commitUserData);
                ++changeCount;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Returns the commit user data map that was last committed, or the one that
        /// was set on <see cref="SetCommitData(IDictionary{string, string})"/>.
        /// </summary>
        public IDictionary<string, string> CommitData
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    return segmentInfos.UserData;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

        /// <summary>
        /// Used only by commit and prepareCommit, below; lock
        /// order is commitLock -> IW
        /// </summary>
        private readonly object commitLock = new object();

        /// <summary>
        /// <para>Commits all pending changes (added &amp; deleted
        /// documents, segment merges, added
        /// indexes, etc.) to the index, and syncs all referenced
        /// index files, such that a reader will see the changes
        /// and the index updates will survive an OS or machine
        /// crash or power loss.  Note that this does not wait for
        /// any running background merges to finish.  This may be a
        /// costly operation, so you should test the cost in your
        /// application and do it only when really necessary.</para>
        ///
        /// <para> Note that this operation calls <see cref="Store.Directory.Sync(ICollection{string})"/> on
        /// the index files.  That call should not return until the
        /// file contents &amp; metadata are on stable storage.  For
        /// <see cref="Store.FSDirectory"/>, this calls the OS's fsync.  But, beware:
        /// some hardware devices may in fact cache writes even
        /// during fsync, and return before the bits are actually
        /// on stable storage, to give the appearance of faster
        /// performance.  If you have such a device, and it does
        /// not have a battery backup (for example) then on power
        /// loss it may still lose data.  Lucene cannot guarantee
        /// consistency on such devices.  </para>
        ///
        /// <para><b>NOTE</b>: if this method hits an <see cref="OutOfMemoryException"/>
        /// you should immediately dispose the writer.  See
        /// <see cref="IndexWriter"/> for details.</para>
        /// </summary>
        public void Commit()
        {
            EnsureOpen();
            CommitInternal();
        }

        /// <summary>
        /// Returns <c>true</c> if there may be changes that have not been
        /// committed.  There are cases where this may return <c>true</c>
        /// when there are no actual "real" changes to the index,
        /// for example if you've deleted by <see cref="Term"/> or <see cref="Query"/> but
        /// that <see cref="Term"/> or <see cref="Query"/> does not match any documents.
        /// Also, if a merge kicked off as a result of flushing a
        /// new segment during <see cref="Commit()"/>, or a concurrent
        /// merged finished, this method may return <c>true</c> right
        /// after you had just called <see cref="Commit()"/>.
        /// </summary>
        public bool HasUncommittedChanges()
        {
            return changeCount != lastCommitChangeCount || docWriter.AnyChanges() || bufferedUpdatesStream.Any();
        }

        private void CommitInternal()
        {
            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "commit: start");
            }

            UninterruptableMonitor.Enter(commitLock);
            try
            {
                EnsureOpen(false);

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "commit: enter lock");
                }

                if (pendingCommit is null)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "commit: now prepare");
                    }
                    PrepareCommitInternal();
                }
                else
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "commit: already prepared");
                    }
                }

                FinishCommit();
            }
            finally
            {
                UninterruptableMonitor.Exit(commitLock);
            }
        }

        private void FinishCommit()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (pendingCommit != null)
                {
                    try
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "commit: pendingCommit != null");
                        }
                        pendingCommit.FinishCommit(directory);
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "commit: wrote segments file \"" + pendingCommit.GetSegmentsFileName() + "\"");
                        }
                        segmentInfos.UpdateGeneration(pendingCommit);
                        lastCommitChangeCount = pendingCommitChangeCount;
                        rollbackSegments = pendingCommit.CreateBackupSegmentInfos();
                        // NOTE: don't use this.checkpoint() here, because
                        // we do not want to increment changeCount:
                        deleter.Checkpoint(pendingCommit, true);
                    }
                    finally
                    {
                        // Matches the incRef done in prepareCommit:
                        deleter.DecRef(filesToCommit);
                        filesToCommit = null;
                        pendingCommit = null;
                        UninterruptableMonitor.PulseAll(this);
                    }
                }
                else
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "commit: pendingCommit is null; skip");
                    }
                }

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "commit: done");
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Ensures only one <see cref="Flush(bool, bool)"/> is actually flushing segments
        /// at a time:
        /// </summary>
        private readonly object fullFlushLock = new object();

        // for assert
        internal virtual bool HoldsFullFlushLock => UninterruptableMonitor.IsEntered(fullFlushLock);

        /// <summary>
        /// Flush all in-memory buffered updates (adds and deletes)
        /// to the <see cref="Store.Directory"/>. </summary>
        /// <param name="triggerMerge"> if <c>true</c>, we may merge segments (if
        /// deletes or docs were flushed) if necessary </param>
        /// <param name="applyAllDeletes"> whether pending deletes should also </param>
        [MethodImpl(MethodImplOptions.NoInlining)]
        public void Flush(bool triggerMerge, bool applyAllDeletes)
        {
            // NOTE: this method cannot be sync'd because
            // maybeMerge() in turn calls mergeScheduler.merge which
            // in turn can take a long time to run and we don't want
            // to hold the lock for that.  In the case of
            // ConcurrentMergeScheduler this can lead to deadlock
            // when it stalls due to too many running merges.

            // We can be called during close, when closing==true, so we must pass false to ensureOpen:
            EnsureOpen(false);
            if (DoFlush(applyAllDeletes) && triggerMerge)
            {
                MaybeMerge(MergeTrigger.FULL_FLUSH, UNBOUNDED_MAX_MERGE_SEGMENTS);
            }
        }

        private bool DoFlush(bool applyAllDeletes)
        {
            if (hitOOM)
            {
                throw IllegalStateException.Create("this writer hit an OutOfMemoryError; cannot flush");
            }

            DoBeforeFlush();
            // LUCENENET: .NET doesn't support asserts in release mode
            if (Lucene.Net.Diagnostics.Debugging.AssertsEnabled) TestPoint("startDoFlush");
            bool success = false;
            try
            {
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "  start flush: applyAllDeletes=" + applyAllDeletes);
                    infoStream.Message("IW", "  index before flush " + SegString());
                }
                bool anySegmentFlushed;

                UninterruptableMonitor.Enter(fullFlushLock);
                try
                {
                    bool flushSuccess = false;
                    try
                    {
                        anySegmentFlushed = docWriter.FlushAllThreads(this);
                        flushSuccess = true;
                    }
                    finally
                    {
                        docWriter.FinishFullFlush(flushSuccess);
                        ProcessEvents(false, true);
                    }
                }
                finally
                {
                    UninterruptableMonitor.Exit(fullFlushLock);
                }
                UninterruptableMonitor.Enter(this);
                try
                {
                    MaybeApplyDeletes(applyAllDeletes);
                    DoAfterFlush();
                    if (!anySegmentFlushed)
                    {
                        // flushCount is incremented in flushAllThreads
                        flushCount.IncrementAndGet();
                    }
                    success = true;
                    return anySegmentFlushed;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "DoFlush");
                // never hit
                return false;
            }
            finally
            {
                if (!success)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "hit exception during flush");
                    }
                }
            }
        }

        internal void MaybeApplyDeletes(bool applyAllDeletes)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (applyAllDeletes)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "apply all deletes during flush");
                    }
                    ApplyAllDeletesAndUpdates();
                }
                else if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "don't apply deletes now delTermCount=" + bufferedUpdatesStream.NumTerms + " bytesUsed=" + bufferedUpdatesStream.BytesUsed);
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        internal void ApplyAllDeletesAndUpdates()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                flushDeletesCount.IncrementAndGet();
                BufferedUpdatesStream.ApplyDeletesResult result;
                result = bufferedUpdatesStream.ApplyDeletesAndUpdates(readerPool, segmentInfos.AsList());
                if (result.AnyDeletes)
                {
                    Checkpoint();
                }
                if (!keepFullyDeletedSegments && result.AllDeleted != null)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "drop 100% deleted segments: " + SegString(result.AllDeleted));
                    }
                    foreach (SegmentCommitInfo info in result.AllDeleted)
                    {
                        // If a merge has already registered for this
                        // segment, we leave it in the readerPool; the
                        // merge will skip merging it and will then drop
                        // it once it's done:
                        if (!mergingSegments.Contains(info))
                        {
                            segmentInfos.Remove(info);
                            readerPool.Drop(info);
                        }
                    }
                    Checkpoint();
                }
                bufferedUpdatesStream.Prune(segmentInfos);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Expert:  Return the total size of all index files currently cached in memory.
        /// Useful for size management with flushRamDocs()
        /// </summary>
        public long RamSizeInBytes()
        {
            EnsureOpen();
            return docWriter.flushControl.NetBytes + bufferedUpdatesStream.BytesUsed;
        }

        // for testing only
        internal virtual DocumentsWriter DocsWriter
            => Debugging.AssertsEnabled ? docWriter : null; // LUCENENET specific - just read the status, simpler than using Assert() to set a local variable

        /// <summary>
        /// Expert:  Return the number of documents currently
        /// buffered in RAM.
        /// </summary>
        public int NumRamDocs()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                EnsureOpen();
                return docWriter.NumDocs;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void EnsureValidMerge(MergePolicy.OneMerge merge)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                foreach (SegmentCommitInfo info in merge.Segments)
                {
                    if (!segmentInfos.Contains(info))
                    {
                        throw new MergePolicy.MergeException("MergePolicy selected a segment (" + info.Info.Name + ") that is not in the current index " + SegString(), directory);
                    }
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private static void SkipDeletedDoc(DocValuesFieldUpdatesIterator[] updatesIters, int deletedDoc) // LUCENENET: CA1822: Mark members as static
        {
            foreach (DocValuesFieldUpdatesIterator iter in updatesIters)
            {
                if (iter.Doc == deletedDoc)
                {
                    iter.NextDoc();
                }
                // when entering the method, all iterators must already be beyond the
                // deleted document, or right on it, in which case we advance them over
                // and they must be beyond it now.
                if (Debugging.AssertsEnabled) Debugging.Assert(iter.Doc > deletedDoc,"updateDoc={0} deletedDoc={1}", iter.Doc, deletedDoc);
            }
        }

        private class MergedDeletesAndUpdates
        {
            internal ReadersAndUpdates mergedDeletesAndUpdates = null;
            internal MergePolicy.DocMap docMap = null;
            internal bool initializedWritableLiveDocs = false;

            internal MergedDeletesAndUpdates()
            {
            }

            internal void Init(ReaderPool readerPool, MergePolicy.OneMerge merge, MergeState mergeState, bool initWritableLiveDocs)
            {
                if (mergedDeletesAndUpdates is null)
                {
                    mergedDeletesAndUpdates = readerPool.Get(merge.info, true);
                    docMap = merge.GetDocMap(mergeState);
                    if (Debugging.AssertsEnabled) Debugging.Assert(docMap.IsConsistent(merge.info.Info.DocCount));
                }
                if (initWritableLiveDocs && !initializedWritableLiveDocs)
                {
                    mergedDeletesAndUpdates.InitWritableLiveDocs();
                    this.initializedWritableLiveDocs = true;
                }
            }
        }

        private void MaybeApplyMergedDVUpdates(MergePolicy.OneMerge merge, MergeState mergeState, int docUpto, MergedDeletesAndUpdates holder, string[] mergingFields, DocValuesFieldUpdates[] dvFieldUpdates, DocValuesFieldUpdatesIterator[] updatesIters, int curDoc)
        {
            int newDoc = -1;
            for (int idx = 0; idx < mergingFields.Length; idx++)
            {
                DocValuesFieldUpdatesIterator updatesIter = updatesIters[idx];
                if (updatesIter.Doc == curDoc) // document has an update
                {
                    if (holder.mergedDeletesAndUpdates is null)
                    {
                        holder.Init(readerPool, merge, mergeState, false);
                    }
                    if (newDoc == -1) // map once per all field updates, but only if there are any updates
                    {
                        newDoc = holder.docMap.Map(docUpto);
                    }
                    DocValuesFieldUpdates dvUpdates = dvFieldUpdates[idx];
                    // LUCENENET specific - dvUpdates handles getting the value so we don't need to deal with boxing/unboxing here.
                    dvUpdates.AddFromIterator(newDoc, updatesIter);
                    updatesIter.NextDoc(); // advance to next document
                }
                else
                {
                    if (Debugging.AssertsEnabled) Debugging.Assert(updatesIter.Doc > curDoc, "field={0} updateDoc={1} curDoc={2}", mergingFields[idx], updatesIter.Doc, curDoc);
                }
            }
        }

        /// <summary>
        /// Carefully merges deletes and updates for the segments we just merged. This
        /// is tricky because, although merging will clear all deletes (compacts the
        /// documents) and compact all the updates, new deletes and updates may have
        /// been flushed to the segments since the merge was started. This method
        /// "carries over" such new deletes and updates onto the newly merged segment,
        /// and saves the resulting deletes and updates files (incrementing the delete
        /// and DV generations for merge.info). If no deletes were flushed, no new
        /// deletes file is saved.
        /// </summary>
        private ReadersAndUpdates CommitMergedDeletesAndUpdates(MergePolicy.OneMerge merge, MergeState mergeState)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (Debugging.AssertsEnabled) Debugging.Assert(TestPoint("startCommitMergeDeletes"));

                IList<SegmentCommitInfo> sourceSegments = merge.Segments;

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "commitMergeDeletes " + SegString(merge.Segments));
                }

                // Carefully merge deletes that occurred after we
                // started merging:
                int docUpto = 0;
                long minGen = long.MaxValue;

                // Lazy init (only when we find a delete to carry over):
                MergedDeletesAndUpdates holder = new MergedDeletesAndUpdates();
                DocValuesFieldUpdates.Container mergedDVUpdates = new DocValuesFieldUpdates.Container();

                for (int i = 0; i < sourceSegments.Count; i++)
                {
                    SegmentCommitInfo info = sourceSegments[i];
                    minGen = Math.Min(info.BufferedDeletesGen, minGen);
                    int docCount = info.Info.DocCount;
                    IBits prevLiveDocs = merge.readers[i].LiveDocs;
                    ReadersAndUpdates rld = readerPool.Get(info, false);
                    // We hold a ref so it should still be in the pool:
                    if (Debugging.AssertsEnabled) Debugging.Assert(rld != null, "seg={0}", info.Info.Name);
                    IBits currentLiveDocs = rld.LiveDocs;
                    IDictionary<string, DocValuesFieldUpdates> mergingFieldUpdates = rld.MergingFieldUpdates;
                    string[] mergingFields;
                    DocValuesFieldUpdates[] dvFieldUpdates;
                    DocValuesFieldUpdatesIterator[] updatesIters;
                    if (mergingFieldUpdates.Count == 0)
                    {
                        mergingFields = null;
                        updatesIters = null;
                        dvFieldUpdates = null;
                    }
                    else
                    {
                        mergingFields = new string[mergingFieldUpdates.Count];
                        dvFieldUpdates = new DocValuesFieldUpdates[mergingFieldUpdates.Count];
                        updatesIters = new DocValuesFieldUpdatesIterator[mergingFieldUpdates.Count];
                        int idx = 0;
                        foreach (KeyValuePair<string, DocValuesFieldUpdates> e in mergingFieldUpdates)
                        {
                            string field = e.Key;
                            DocValuesFieldUpdates updates = e.Value;
                            mergingFields[idx] = field;
                            dvFieldUpdates[idx] = mergedDVUpdates.GetUpdates(field, updates.type);
                            if (dvFieldUpdates[idx] is null)
                            {
                                dvFieldUpdates[idx] = mergedDVUpdates.NewUpdates(field, updates.type, mergeState.SegmentInfo.DocCount);
                            }
                            updatesIters[idx] = updates.GetIterator();
                            updatesIters[idx].NextDoc(); // advance to first update doc
                            ++idx;
                        }
                    }
                    //      System.out.println("[" + Thread.currentThread().getName() + "] IW.commitMergedDeletes: info=" + info + ", mergingUpdates=" + mergingUpdates);

                    if (prevLiveDocs != null)
                    {
                        // If we had deletions on starting the merge we must
                        // still have deletions now:
                        if (Debugging.AssertsEnabled)
                        {
                            Debugging.Assert(currentLiveDocs != null);
                            Debugging.Assert(prevLiveDocs.Length == docCount);
                            Debugging.Assert(currentLiveDocs.Length == docCount);
                        }

                        // There were deletes on this segment when the merge
                        // started.  The merge has collapsed away those
                        // deletes, but, if new deletes were flushed since
                        // the merge started, we must now carefully keep any
                        // newly flushed deletes but mapping them to the new
                        // docIDs.

                        // Since we copy-on-write, if any new deletes were
                        // applied after merging has started, we can just
                        // check if the before/after liveDocs have changed.
                        // If so, we must carefully merge the liveDocs one
                        // doc at a time:
                        if (currentLiveDocs != prevLiveDocs)
                        {
                            // this means this segment received new deletes
                            // since we started the merge, so we
                            // must merge them:
                            for (int j = 0; j < docCount; j++)
                            {
                                if (!prevLiveDocs.Get(j))
                                {
                                    if (Debugging.AssertsEnabled) Debugging.Assert(!currentLiveDocs.Get(j));
                                }
                                else
                                {
                                    if (!currentLiveDocs.Get(j))
                                    {
                                        if (holder.mergedDeletesAndUpdates is null || !holder.initializedWritableLiveDocs)
                                        {
                                            holder.Init(readerPool, merge, mergeState, true);
                                        }
                                        holder.mergedDeletesAndUpdates.Delete(holder.docMap.Map(docUpto));
                                        if (mergingFields != null) // advance all iters beyond the deleted document
                                        {
                                            SkipDeletedDoc(updatesIters, j);
                                        }
                                    }
                                    else if (mergingFields != null)
                                    {
                                        MaybeApplyMergedDVUpdates(merge, mergeState, docUpto, holder, mergingFields, dvFieldUpdates, updatesIters, j);
                                    }
                                    docUpto++;
                                }
                            }
                        }
                        else if (mergingFields != null)
                        {
                            // need to check each non-deleted document if it has any updates
                            for (int j = 0; j < docCount; j++)
                            {
                                if (prevLiveDocs.Get(j))
                                {
                                    // document isn't deleted, check if any of the fields have an update to it
                                    MaybeApplyMergedDVUpdates(merge, mergeState, docUpto, holder, mergingFields, dvFieldUpdates, updatesIters, j);
                                    // advance docUpto for every non-deleted document
                                    docUpto++;
                                }
                                else
                                {
                                    // advance all iters beyond the deleted document
                                    SkipDeletedDoc(updatesIters, j);
                                }
                            }
                        }
                        else
                        {
                            docUpto += info.Info.DocCount - info.DelCount - rld.PendingDeleteCount;
                        }
                    }
                    else if (currentLiveDocs != null)
                    {
                        if (Debugging.AssertsEnabled) Debugging.Assert(currentLiveDocs.Length == docCount);
                        // this segment had no deletes before but now it
                        // does:
                        for (int j = 0; j < docCount; j++)
                        {
                            if (!currentLiveDocs.Get(j))
                            {
                                if (holder.mergedDeletesAndUpdates is null || !holder.initializedWritableLiveDocs)
                                {
                                    holder.Init(readerPool, merge, mergeState, true);
                                }
                                holder.mergedDeletesAndUpdates.Delete(holder.docMap.Map(docUpto));
                                if (mergingFields != null) // advance all iters beyond the deleted document
                                {
                                    SkipDeletedDoc(updatesIters, j);
                                }
                            }
                            else if (mergingFields != null)
                            {
                                MaybeApplyMergedDVUpdates(merge, mergeState, docUpto, holder, mergingFields, dvFieldUpdates, updatesIters, j);
                            }
                            docUpto++;
                        }
                    }
                    else if (mergingFields != null)
                    {
                        // no deletions before or after, but there were updates
                        for (int j = 0; j < docCount; j++)
                        {
                            MaybeApplyMergedDVUpdates(merge, mergeState, docUpto, holder, mergingFields, dvFieldUpdates, updatesIters, j);
                            // advance docUpto for every non-deleted document
                            docUpto++;
                        }
                    }
                    else
                    {
                        // No deletes or updates before or after
                        docUpto += info.Info.DocCount;
                    }
                }

                if (Debugging.AssertsEnabled) Debugging.Assert(docUpto == merge.info.Info.DocCount);

                if (mergedDVUpdates.Any())
                {
                    //      System.out.println("[" + Thread.currentThread().getName() + "] IW.commitMergedDeletes: mergedDeletes.info=" + mergedDeletes.info + ", mergedFieldUpdates=" + mergedFieldUpdates);
                    bool success = false;
                    try
                    {
                        // if any error occurs while writing the field updates we should release
                        // the info, otherwise it stays in the pool but is considered not "live"
                        // which later causes false exceptions in pool.dropAll().
                        // NOTE: currently this is the only place which throws a true
                        // IOException. If this ever changes, we need to extend that try/finally
                        // block to the rest of the method too.
                        holder.mergedDeletesAndUpdates.WriteFieldUpdates(directory, mergedDVUpdates);
                        success = true;
                    }
                    finally
                    {
                        if (!success)
                        {
                            holder.mergedDeletesAndUpdates.DropChanges();
                            readerPool.Drop(merge.info);
                        }
                    }
                }

                if (infoStream.IsEnabled("IW"))
                {
                    if (holder.mergedDeletesAndUpdates is null)
                    {
                        infoStream.Message("IW", "no new deletes or field updates since merge started");
                    }
                    else
                    {
                        string msg = holder.mergedDeletesAndUpdates.PendingDeleteCount + " new deletes";
                        if (mergedDVUpdates.Any())
                        {
                            msg += " and " + mergedDVUpdates.Count + " new field updates";
                        }
                        msg += " since merge started";
                        infoStream.Message("IW", msg);
                    }
                }

                merge.info.SetBufferedDeletesGen(minGen);

                return holder.mergedDeletesAndUpdates;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private bool CommitMerge(MergePolicy.OneMerge merge, MergeState mergeState)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (Debugging.AssertsEnabled) Debugging.Assert(TestPoint("startCommitMerge"));

                if (hitOOM)
                {
                    throw IllegalStateException.Create("this writer hit an OutOfMemoryError; cannot complete merge");
                }

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "commitMerge: " + SegString(merge.Segments) + " index=" + SegString());
                }

                if (Debugging.AssertsEnabled) Debugging.Assert(merge.registerDone);

                // If merge was explicitly aborted, or, if rollback() or
                // rollbackTransaction() had been called since our merge
                // started (which results in an unqualified
                // deleter.refresh() call that will remove any index
                // file that current segments does not reference), we
                // abort this merge
                if (merge.IsAborted)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "commitMerge: skip: it was aborted");
                    }
                    // In case we opened and pooled a reader for this
                    // segment, drop it now.  this ensures that we close
                    // the reader before trying to delete any of its
                    // files.  this is not a very big deal, since this
                    // reader will never be used by any NRT reader, and
                    // another thread is currently running close(false)
                    // so it will be dropped shortly anyway, but not
                    // doing this  makes  MockDirWrapper angry in
                    // TestNRTThreads (LUCENE-5434):
                    readerPool.Drop(merge.info);
                    deleter.DeleteNewFiles(merge.info.GetFiles());
                    return false;
                }

                ReadersAndUpdates mergedUpdates = merge.info.Info.DocCount == 0 ? null : CommitMergedDeletesAndUpdates(merge, mergeState);
                //    System.out.println("[" + Thread.currentThread().getName() + "] IW.commitMerge: mergedDeletes=" + mergedDeletes);

                // If the doc store we are using has been closed and
                // is in now compound format (but wasn't when we
                // started), then we will switch to the compound
                // format as well:

                if (Debugging.AssertsEnabled) Debugging.Assert(!segmentInfos.Contains(merge.info));

                bool allDeleted = merge.Segments.Count == 0 || merge.info.Info.DocCount == 0 || (mergedUpdates != null && mergedUpdates.PendingDeleteCount == merge.info.Info.DocCount);

                if (infoStream.IsEnabled("IW"))
                {
                    if (allDeleted)
                    {
                        infoStream.Message("IW", "merged segment " + merge.info + " is 100% deleted" + (keepFullyDeletedSegments ? "" : "; skipping insert"));
                    }
                }

                bool dropSegment = allDeleted && !keepFullyDeletedSegments;

                // If we merged no segments then we better be dropping
                // the new segment:
                if (Debugging.AssertsEnabled) Debugging.Assert(merge.Segments.Count > 0 || dropSegment);

                if (Debugging.AssertsEnabled) Debugging.Assert(merge.info.Info.DocCount != 0 || keepFullyDeletedSegments || dropSegment);

                if (mergedUpdates != null)
                {
                    bool success = false;
                    try
                    {
                        if (dropSegment)
                        {
                            mergedUpdates.DropChanges();
                        }
                        // Pass false for assertInfoLive because the merged
                        // segment is not yet live (only below do we commit it
                        // to the segmentInfos):
                        readerPool.Release(mergedUpdates, false);
                        success = true;
                    }
                    finally
                    {
                        if (!success)
                        {
                            mergedUpdates.DropChanges();
                            readerPool.Drop(merge.info);
                        }
                    }
                }

                // Must do this after readerPool.release, in case an
                // exception is hit e.g. writing the live docs for the
                // merge segment, in which case we need to abort the
                // merge:
                segmentInfos.ApplyMergeChanges(merge, dropSegment);

                if (dropSegment)
                {
                    if (Debugging.AssertsEnabled) Debugging.Assert(!segmentInfos.Contains(merge.info));
                    readerPool.Drop(merge.info);
                    deleter.DeleteNewFiles(merge.info.GetFiles());
                }

                bool success_ = false;
                try
                {
                    // Must close before checkpoint, otherwise IFD won't be
                    // able to delete the held-open files from the merge
                    // readers:
                    CloseMergeReaders(merge, false);
                    success_ = true;
                }
                finally
                {
                    // Must note the change to segmentInfos so any commits
                    // in-flight don't lose it (IFD will incRef/protect the
                    // new files we created):
                    if (success_)
                    {
                        Checkpoint();
                    }
                    else
                    {
                        try
                        {
                            Checkpoint();
                        }
                        catch (Exception t) when (t.IsThrowable())
                        {
                            // Ignore so we keep throwing original exception.
                        }
                    }
                }

                deleter.DeletePendingFiles();

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "after commitMerge: " + SegString());
                }

                if (merge.MaxNumSegments != -1 && !dropSegment)
                {
                    // cascade the forceMerge:
                    if (!segmentsToMerge.ContainsKey(merge.info))
                    {
                        segmentsToMerge[merge.info] = false;
                    }
                }

                return true;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void HandleMergeException(Exception t, MergePolicy.OneMerge merge)
        {
            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "handleMergeException: merge=" + SegString(merge.Segments) + " exc=" + t);
            }

            // Set the exception on the merge, so if
            // forceMerge is waiting on us it sees the root
            // cause exception:
            merge.Exception = t;
            AddMergeException(merge);

            if ((t as MergePolicy.MergeAbortedException) != null)
            {
                // We can ignore this exception (it happens when
                // close(false) or rollback is called), unless the
                // merge involves segments from external directories,
                // in which case we must throw it so, for example, the
                // rollbackTransaction code in addIndexes* is
                // executed.
                if (merge.isExternal)
                {
                    ExceptionDispatchInfo.Capture(t).Throw(); // LUCENENET: Rethrow to preserve stack details from the original throw
                }
            }
            else
            {
                IOUtils.ReThrow(t);
            }
        }

        /// <summary>
        /// Merges the indicated segments, replacing them in the stack with a
        /// single segment.
        /// <para/>
        /// @lucene.experimental
        /// </summary>
        [MethodImpl(MethodImplOptions.NoInlining)]
        public virtual void Merge(MergePolicy.OneMerge merge)
        {
            bool success = false;

            long t0 = Time.NanoTime() / Time.MillisecondsPerNanosecond; // LUCENENET: Use NanoTime() rather than CurrentTimeMilliseconds() for more accurate/reliable results

            try
            {
                try
                {
                    try
                    {
                        MergeInit(merge);
                        //if (merge.info != null) {
                        //System.out.println("MERGE: " + merge.info.info.name);
                        //}

                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "now merge\n  merge=" + SegString(merge.Segments) + "\n  index=" + SegString());
                        }

                        MergeMiddle(merge);
                        MergeSuccess(merge);
                        success = true;
                    }
                    catch (Exception t) when (t.IsThrowable())
                    {
                        HandleMergeException(t, merge);
                    }
                }
                finally
                {
                    UninterruptableMonitor.Enter(this);
                    try
                    {
                        MergeFinish(merge);

                        if (!success)
                        {
                            if (infoStream.IsEnabled("IW"))
                            {
                                infoStream.Message("IW", "hit exception during merge");
                            }
                            if (merge.info != null && !segmentInfos.Contains(merge.info))
                            {
                                deleter.Refresh(merge.info.Info.Name);
                            }
                        }

                        // this merge (and, generally, any change to the
                        // segments) may now enable new merges, so we call
                        // merge policy & update pending merges.
                        if (success && !merge.IsAborted && (merge.MaxNumSegments != -1 || (!closed && !closing)))
                        {
                            UpdatePendingMerges(MergeTrigger.MERGE_FINISHED, merge.MaxNumSegments);
                        }
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(this);
                    }
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "Merge");
            }
            if (merge.info != null && !merge.IsAborted)
            {
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "merge time " + ((Time.NanoTime() / Time.MillisecondsPerNanosecond) - t0) + " msec for " + merge.info.Info.DocCount + " docs"); // LUCENENET: Use NanoTime() rather than CurrentTimeMilliseconds() for more accurate/reliable results
                }
            }
        }

        /// <summary>
        /// Hook that's called when the specified merge is complete. </summary>
        internal virtual void MergeSuccess(MergePolicy.OneMerge merge)
        {
        }

        /// <summary>
        /// Checks whether this merge involves any segments
        /// already participating in a merge.  If not, this merge
        /// is "registered", meaning we record that its segments
        /// are now participating in a merge, and <c>true</c> is
        /// returned.  Else (the merge conflicts) <c>false</c> is
        /// returned.
        /// </summary>
        internal bool RegisterMerge(MergePolicy.OneMerge merge)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (merge.registerDone)
                {
                    return true;
                }
                if (Debugging.AssertsEnabled) Debugging.Assert(merge.Segments.Count > 0);

                if (stopMerges)
                {
                    merge.Abort();
                    throw new MergePolicy.MergeAbortedException("merge is aborted: " + SegString(merge.Segments));
                }

                bool isExternal = false;
                foreach (SegmentCommitInfo info in merge.Segments)
                {
                    if (mergingSegments.Contains(info))
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "reject merge " + SegString(merge.Segments) + ": segment " + SegString(info) + " is already marked for merge");
                        }
                        return false;
                    }
                    if (!segmentInfos.Contains(info))
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "reject merge " + SegString(merge.Segments) + ": segment " + SegString(info) + " does not exist in live infos");
                        }
                        return false;
                    }
                    if (info.Info.Dir != directory)
                    {
                        isExternal = true;
                    }
                    if (segmentsToMerge.ContainsKey(info))
                    {
                        merge.MaxNumSegments = mergeMaxNumSegments;
                    }
                }

                EnsureValidMerge(merge);

                pendingMerges.Enqueue(merge);

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "add merge to pendingMerges: " + SegString(merge.Segments) + " [total " + pendingMerges.Count + " pending]");
                }

                merge.mergeGen = mergeGen;
                merge.isExternal = isExternal;

                // OK it does not conflict; now record that this merge
                // is running (while synchronized) to avoid race
                // condition where two conflicting merges from different
                // threads, start
                if (infoStream.IsEnabled("IW"))
                {
                    StringBuilder builder = new StringBuilder("registerMerge merging= [");
                    foreach (SegmentCommitInfo info in mergingSegments)
                    {
                        builder.Append(info.Info.Name).Append(", ");
                    }
                    builder.Append(']');
                    // don't call mergingSegments.toString() could lead to ConcurrentModException
                    // since merge updates the segments FieldInfos
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", builder.ToString());
                    }
                }
                foreach (SegmentCommitInfo info in merge.Segments)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "registerMerge info=" + SegString(info));
                    }
                    mergingSegments.Add(info);
                }

                if (Debugging.AssertsEnabled)
                {
                    Debugging.Assert(merge.EstimatedMergeBytes == 0);
                    Debugging.Assert(merge.totalMergeBytes == 0);
                }
                foreach (SegmentCommitInfo info in merge.Segments)
                {
                    if (info.Info.DocCount > 0)
                    {
                        int delCount = NumDeletedDocs(info);
                        if (Debugging.AssertsEnabled) Debugging.Assert(delCount <= info.Info.DocCount);
                        double delRatio = ((double)delCount) / info.Info.DocCount;
                        merge.EstimatedMergeBytes += (long)(info.GetSizeInBytes() * (1.0 - delRatio));
                        merge.totalMergeBytes += info.GetSizeInBytes();
                    }
                }

                // Merge is now registered
                merge.registerDone = true;

                return true;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Does initial setup for a merge, which is fast but holds
        /// the synchronized lock on <see cref="IndexWriter"/> instance.
        /// </summary>
        internal void MergeInit(MergePolicy.OneMerge merge)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                bool success = false;
                try
                {
                    MergeInitImpl(merge);
                    success = true;
                }
                finally
                {
                    if (!success)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "hit exception in mergeInit");
                        }
                        MergeFinish(merge);
                    }
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void MergeInitImpl(MergePolicy.OneMerge merge) // LUCENENET specific: renamed from _mergeInit
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (Debugging.AssertsEnabled)
                {
                    Debugging.Assert(TestPoint("startMergeInit"));

                    Debugging.Assert(merge.registerDone);
                    Debugging.Assert(merge.MaxNumSegments == -1 || merge.MaxNumSegments > 0);
                }

                if (hitOOM)
                {
                    throw IllegalStateException.Create("this writer hit an OutOfMemoryError; cannot merge");
                }

                if (merge.info != null)
                {
                    // mergeInit already done
                    return;
                }

                if (merge.IsAborted)
                {
                    return;
                }

                // TODO: in the non-pool'd case this is somewhat
                // wasteful, because we open these readers, close them,
                // and then open them again for merging.  Maybe  we
                // could pre-pool them somehow in that case...

                // Lock order: IW -> BD
                BufferedUpdatesStream.ApplyDeletesResult result = bufferedUpdatesStream.ApplyDeletesAndUpdates(readerPool, merge.Segments);

                if (result.AnyDeletes)
                {
                    Checkpoint();
                }

                if (!keepFullyDeletedSegments && result.AllDeleted != null)
                {
                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "drop 100% deleted segments: " + result.AllDeleted);
                    }
                    foreach (SegmentCommitInfo info in result.AllDeleted)
                    {
                        segmentInfos.Remove(info);
                        if (merge.Segments.Contains(info))
                        {
                            mergingSegments.Remove(info);
                            merge.Segments.Remove(info);
                        }
                        readerPool.Drop(info);
                    }
                    Checkpoint();
                }

                // Bind a new segment name here so even with
                // ConcurrentMergePolicy we keep deterministic segment
                // names.
                string mergeSegmentName = NewSegmentName();
                SegmentInfo si = new SegmentInfo(directory, Constants.LUCENE_MAIN_VERSION, mergeSegmentName, -1, false, codec, null);
                IDictionary<string, string> details = new Dictionary<string, string>
                {
                    ["mergeMaxNumSegments"] = "" + merge.MaxNumSegments,
                    ["mergeFactor"] = Convert.ToString(merge.Segments.Count)
                };
                SetDiagnostics(si, SOURCE_MERGE, details);
                merge.Info = new SegmentCommitInfo(si, 0, -1L, -1L);

                //    System.out.println("[" + Thread.currentThread().getName() + "] IW._mergeInit: " + segString(merge.segments) + " into " + si);

                // Lock order: IW -> BD
                bufferedUpdatesStream.Prune(segmentInfos);

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "merge seg=" + merge.info.Info.Name + " " + SegString(merge.Segments));
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        internal static void SetDiagnostics(SegmentInfo info, string source)
        {
            SetDiagnostics(info, source, null);
        }

        private static void SetDiagnostics(SegmentInfo info, string source, IDictionary<string, string> details)
        {
            IDictionary<string, string> diagnostics = new Dictionary<string, string>
            {
                ["source"] = source,
                ["lucene.version"] = Constants.LUCENE_VERSION,
                ["os"] = Constants.OS_NAME,
                ["os.arch"] = Constants.OS_ARCH,
                ["os.version"] = Constants.OS_VERSION,
                ["java.version"] = Constants.RUNTIME_VERSION,
                ["java.vendor"] = Constants.RUNTIME_VENDOR,
                ["timestamp"] = Convert.ToString((DateTime.Now))
            };
            if (details != null)
            {
                diagnostics.PutAll(details);
            }
            info.Diagnostics = diagnostics;
        }

        /// <summary>
        /// Does fininishing for a merge, which is fast but holds
        /// the synchronized lock on <see cref="IndexWriter"/> instance.
        /// </summary>
        public void MergeFinish(MergePolicy.OneMerge merge)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                // forceMerge, addIndexes or finishMerges may be waiting
                // on merges to finish.
                UninterruptableMonitor.PulseAll(this);

                // It's possible we are called twice, eg if there was an
                // exception inside mergeInit
                if (merge.registerDone)
                {
                    IList<SegmentCommitInfo> sourceSegments = merge.Segments;
                    foreach (SegmentCommitInfo info in sourceSegments)
                    {
                        mergingSegments.Remove(info);
                    }
                    merge.registerDone = false;
                }

                runningMerges.Remove(merge);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void CloseMergeReaders(MergePolicy.OneMerge merge, bool suppressExceptions)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                int numSegments = merge.readers.Count;
                Exception th = null;

                bool drop = !suppressExceptions;

                for (int i = 0; i < numSegments; i++)
                {
                    SegmentReader sr = merge.readers[i];
                    if (sr != null)
                    {
                        try
                        {
                            ReadersAndUpdates rld = readerPool.Get(sr.SegmentInfo, false);
                            // We still hold a ref so it should not have been removed:
                            if (Debugging.AssertsEnabled) Debugging.Assert(rld != null);
                            if (drop)
                            {
                                rld.DropChanges();
                            }
                            else
                            {
                                rld.DropMergingUpdates();
                            }
                            rld.Release(sr);
                            readerPool.Release(rld);
                            if (drop)
                            {
                                readerPool.Drop(rld.Info);
                            }
                        }
                        catch (Exception t) when (t.IsThrowable())
                        {
                            if (th is null)
                            {
                                th = t;
                            }
                        }
                        merge.readers[i] = null;
                    }
                }

                // If any error occured, throw it.
                if (!suppressExceptions)
                {
                    IOUtils.ReThrow(th);
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Does the actual (time-consuming) work of the merge,
        /// but without holding synchronized lock on <see cref="IndexWriter"/>
        /// instance
        /// </summary>
        private int MergeMiddle(MergePolicy.OneMerge merge)
        {
            merge.CheckAborted(directory);

            string mergedName = merge.info.Info.Name;

            IList<SegmentCommitInfo> sourceSegments = merge.Segments;

            IOContext context = new IOContext(merge.MergeInfo);

            CheckAbort checkAbort = new CheckAbort(merge, directory);
            TrackingDirectoryWrapper dirWrapper = new TrackingDirectoryWrapper(directory);

            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "merging " + SegString(merge.Segments));
            }

            merge.readers = new JCG.List<SegmentReader>();

            // this is try/finally to make sure merger's readers are
            // closed:
            bool success = false;
            try
            {
                int segUpto = 0;
                while (segUpto < sourceSegments.Count)
                {
                    SegmentCommitInfo info = sourceSegments[segUpto];

                    // Hold onto the "live" reader; we will use this to
                    // commit merged deletes
                    ReadersAndUpdates rld = readerPool.Get(info, true);

                    // Carefully pull the most recent live docs and reader
                    SegmentReader reader;
                    IBits liveDocs;
                    int delCount;

                    UninterruptableMonitor.Enter(this);
                    try
                    {
                        // Must sync to ensure BufferedDeletesStream cannot change liveDocs,
                        // pendingDeleteCount and field updates while we pull a copy:
                        reader = rld.GetReaderForMerge(context);
                        liveDocs = rld.GetReadOnlyLiveDocs();
                        delCount = rld.PendingDeleteCount + info.DelCount;

                        if (Debugging.AssertsEnabled)
                        {
                            Debugging.Assert(reader != null);
                            Debugging.Assert(rld.VerifyDocCounts());
                        }

                        if (infoStream.IsEnabled("IW"))
                        {
                            if (rld.PendingDeleteCount != 0)
                            {
                                infoStream.Message("IW", "seg=" + SegString(info) + " delCount=" + info.DelCount + " pendingDelCount=" + rld.PendingDeleteCount);
                            }
                            else if (info.DelCount != 0)
                            {
                                infoStream.Message("IW", "seg=" + SegString(info) + " delCount=" + info.DelCount);
                            }
                            else
                            {
                                infoStream.Message("IW", "seg=" + SegString(info) + " no deletes");
                            }
                        }
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(this);
                    }

                    // Deletes might have happened after we pulled the merge reader and
                    // before we got a read-only copy of the segment's actual live docs
                    // (taking pending deletes into account). In that case we need to
                    // make a new reader with updated live docs and del count.
                    if (reader.NumDeletedDocs != delCount)
                    {
                        // fix the reader's live docs and del count
                        if (Debugging.AssertsEnabled) Debugging.Assert(delCount > reader.NumDeletedDocs); // beware of zombies

                        SegmentReader newReader = new SegmentReader(info, reader, liveDocs, info.Info.DocCount - delCount);
                        bool released = false;
                        try
                        {
                            rld.Release(reader);
                            released = true;
                        }
                        finally
                        {
                            if (!released)
                            {
                                newReader.DecRef();
                            }
                        }

                        reader = newReader;
                    }

                    merge.readers.Add(reader);
                    if (Debugging.AssertsEnabled) Debugging.Assert(delCount <= info.Info.DocCount, "delCount={0} info.DocCount={1} rld.PendingDeleteCount={2} info.DelCount=", delCount, info.Info.DocCount, rld.PendingDeleteCount, info.DelCount);
                    segUpto++;
                }

                //      System.out.println("[" + Thread.currentThread().getName() + "] IW.mergeMiddle: merging " + merge.getMergeReaders());

                // we pass merge.getMergeReaders() instead of merge.readers to allow the
                // OneMerge to return a view over the actual segments to merge
                SegmentMerger merger = new SegmentMerger(merge.GetMergeReaders(), merge.info.Info, infoStream, dirWrapper, config.TermIndexInterval, checkAbort, globalFieldNumberMap, context, config.CheckIntegrityAtMerge);

                merge.CheckAborted(directory);

                // this is where all the work happens:
                MergeState mergeState;
                bool success3 = false;
                try
                {
                    if (!merger.ShouldMerge)
                    {
                        // would result in a 0 document segment: nothing to merge!
                        mergeState = new MergeState(new JCG.List<AtomicReader>(), merge.info.Info, infoStream, checkAbort);
                    }
                    else
                    {
                        mergeState = merger.Merge();
                    }
                    success3 = true;
                }
                finally
                {
                    if (!success3)
                    {
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            deleter.Refresh(merge.info.Info.Name);
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                }
                if (Debugging.AssertsEnabled) Debugging.Assert(mergeState.SegmentInfo == merge.info.Info);
                merge.info.Info.SetFiles(new JCG.HashSet<string>(dirWrapper.CreatedFiles));

                // Record which codec was used to write the segment

                if (infoStream.IsEnabled("IW"))
                {
                    if (merge.info.Info.DocCount == 0)
                    {
                        infoStream.Message("IW", "merge away fully deleted segments");
                    }
                    else
                    {
                        infoStream.Message("IW", "merge codec=" + codec + " docCount=" + merge.info.Info.DocCount + "; merged segment has " + (mergeState.FieldInfos.HasVectors ? "vectors" : "no vectors") + "; " + (mergeState.FieldInfos.HasNorms ? "norms" : "no norms") + "; " + (mergeState.FieldInfos.HasDocValues ? "docValues" : "no docValues") + "; " + (mergeState.FieldInfos.HasProx ? "prox" : "no prox") + "; " + (mergeState.FieldInfos.HasProx ? "freqs" : "no freqs"));
                    }
                }

                // Very important to do this before opening the reader
                // because codec must know if prox was written for
                // this segment:
                //System.out.println("merger set hasProx=" + merger.hasProx() + " seg=" + merge.info.name);
                bool useCompoundFile;
                UninterruptableMonitor.Enter(this); // Guard segmentInfos
                try
                {
                    useCompoundFile = mergePolicy.UseCompoundFile(segmentInfos, merge.info);
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                if (useCompoundFile)
                {
                    success = false;

                    ICollection<string> filesToRemove = merge.info.GetFiles();

                    try
                    {
                        filesToRemove = CreateCompoundFile(infoStream, directory, checkAbort, merge.info.Info, context);
                        success = true;
                    }
                    catch (Exception ioe) when (ioe.IsIOException())
                    {
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            if (merge.IsAborted)
                            {
                                // this can happen if rollback or close(false)
                                // is called -- fall through to logic below to
                                // remove the partially created CFS:
                            }
                            else
                            {
                                HandleMergeException(ioe, merge);
                            }
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                    catch (Exception t) when (t.IsThrowable())
                    {
                        HandleMergeException(t, merge);
                    }
                    finally
                    {
                        if (!success)
                        {
                            if (infoStream.IsEnabled("IW"))
                            {
                                infoStream.Message("IW", "hit exception creating compound file during merge");
                            }

                            UninterruptableMonitor.Enter(this);
                            try
                            {
                                deleter.DeleteFile(Lucene.Net.Index.IndexFileNames.SegmentFileName(mergedName, "", Lucene.Net.Index.IndexFileNames.COMPOUND_FILE_EXTENSION));
                                deleter.DeleteFile(Lucene.Net.Index.IndexFileNames.SegmentFileName(mergedName, "", Lucene.Net.Index.IndexFileNames.COMPOUND_FILE_ENTRIES_EXTENSION));
                                deleter.DeleteNewFiles(merge.info.GetFiles());
                            }
                            finally
                            {
                                UninterruptableMonitor.Exit(this);
                            }
                        }
                    }

                    // So that, if we hit exc in deleteNewFiles (next)
                    // or in commitMerge (later), we close the
                    // per-segment readers in the finally clause below:
                    success = false;

                    UninterruptableMonitor.Enter(this);
                    try
                    {
                        // delete new non cfs files directly: they were never
                        // registered with IFD
                        deleter.DeleteNewFiles(filesToRemove);

                        if (merge.IsAborted)
                        {
                            if (infoStream.IsEnabled("IW"))
                            {
                                infoStream.Message("IW", "abort merge after building CFS");
                            }
                            deleter.DeleteFile(Lucene.Net.Index.IndexFileNames.SegmentFileName(mergedName, "", Lucene.Net.Index.IndexFileNames.COMPOUND_FILE_EXTENSION));
                            deleter.DeleteFile(Lucene.Net.Index.IndexFileNames.SegmentFileName(mergedName, "", Lucene.Net.Index.IndexFileNames.COMPOUND_FILE_ENTRIES_EXTENSION));
                            return 0;
                        }
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(this);
                    }

                    merge.info.Info.UseCompoundFile = true;
                }
                else
                {
                    // So that, if we hit exc in commitMerge (later),
                    // we close the per-segment readers in the finally
                    // clause below:
                    success = false;
                }

                // Have codec write SegmentInfo.  Must do this after
                // creating CFS so that 1) .si isn't slurped into CFS,
                // and 2) .si reflects useCompoundFile=true change
                // above:
                bool success2 = false;
                try
                {
                    codec.SegmentInfoFormat.SegmentInfoWriter.Write(directory, merge.info.Info, mergeState.FieldInfos, context);
                    success2 = true;
                }
                finally
                {
                    if (!success2)
                    {
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            deleter.DeleteNewFiles(merge.info.GetFiles());
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                }

                // TODO: ideally we would freeze merge.info here!!
                // because any changes after writing the .si will be
                // lost...

                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", string.Format(CultureInfo.InvariantCulture, "merged segment size={0:n3} MB vs estimate={1:n3} MB", merge.info.GetSizeInBytes() / 1024.0 / 1024.0, merge.EstimatedMergeBytes / 1024 / 1024.0));
                }

                IndexReaderWarmer mergedSegmentWarmer = config.MergedSegmentWarmer;
                if (poolReaders && mergedSegmentWarmer != null && merge.info.Info.DocCount != 0)
                {
                    ReadersAndUpdates rld = readerPool.Get(merge.info, true);
                    SegmentReader sr = rld.GetReader(IOContext.READ);
                    try
                    {
                        mergedSegmentWarmer.Warm(sr);
                    }
                    finally
                    {
                        UninterruptableMonitor.Enter(this);
                        try
                        {
                            rld.Release(sr);
                            readerPool.Release(rld);
                        }
                        finally
                        {
                            UninterruptableMonitor.Exit(this);
                        }
                    }
                }

                // Force READ context because we merge deletes onto
                // this reader:
                if (!CommitMerge(merge, mergeState))
                {
                    // commitMerge will return false if this merge was
                    // aborted
                    return 0;
                }

                success = true;
            }
            finally
            {
                // Readers are already closed in commitMerge if we didn't hit
                // an exc:
                if (!success)
                {
                    CloseMergeReaders(merge, true);
                }
            }

            return merge.info.Info.DocCount;
        }

        internal virtual void AddMergeException(MergePolicy.OneMerge merge)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                if (Debugging.AssertsEnabled) Debugging.Assert(merge.Exception != null);
                if (!mergeExceptions.Contains(merge) && mergeGen == merge.mergeGen)
                {
                    mergeExceptions.Add(merge);
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        // For test purposes.
        internal int BufferedDeleteTermsSize => docWriter.BufferedDeleteTermsSize;

        // For test purposes.
        internal int NumBufferedDeleteTerms => docWriter.NumBufferedDeleteTerms;

        // utility routines for tests
        internal virtual SegmentCommitInfo NewestSegment()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                return segmentInfos.Count > 0 ? segmentInfos[segmentInfos.Count - 1] : null;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Returns a string description of all segments, for
        /// debugging.
        /// <para/>
        /// @lucene.internal
        /// </summary>
        public virtual string SegString()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                return SegString(segmentInfos.Segments);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Returns a string description of the specified
        /// segments, for debugging.
        /// <para/>
        /// @lucene.internal
        /// </summary>
        public virtual string SegString(IEnumerable<SegmentCommitInfo> infos)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                StringBuilder buffer = new StringBuilder();
                foreach (SegmentCommitInfo info in infos)
                {
                    if (buffer.Length > 0)
                    {
                        buffer.Append(' ');
                    }
                    buffer.Append(SegString(info));
                }
                return buffer.ToString();
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        /// <summary>
        /// Returns a string description of the specified
        /// segment, for debugging.
        /// <para/>
        /// @lucene.internal
        /// </summary>
        public virtual string SegString(SegmentCommitInfo info)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                return info.ToString(info.Info.Dir, NumDeletedDocs(info) - info.DelCount);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void DoWait()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                // NOTE: the callers of this method should in theory
                // be able to do simply wait(), but, as a defense
                // against thread timing hazards where notifyAll()
                // fails to be called, we wait for at most 1 second
                // and then return so caller can check if wait
                // conditions are satisfied:
                try
                {
                    UninterruptableMonitor.Wait(this, TimeSpan.FromMilliseconds(1000));
                }
                catch (Exception ie) when (ie.IsInterruptedException())
                {
                    throw new Util.ThreadInterruptedException(ie);
                }
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private bool keepFullyDeletedSegments;

        /// <summary>
        /// Only for testing.
        /// <para/>
        /// @lucene.internal
        /// </summary>
        public virtual bool KeepFullyDeletedSegments
        {
            get => keepFullyDeletedSegments;
            set => keepFullyDeletedSegments = value;
        }

        // called only from assert
        private bool FilesExist(SegmentInfos toSync)
        {
            ICollection<string> files = toSync.GetFiles(directory, false);
            foreach (string fileName in files)
            {
                if (Debugging.AssertsEnabled)
                {
                    // LUCENENET specific - use Directory.ListAllFormatter to defer directory listing/string building until after the condition fails
                    Debugging.Assert(SlowFileExists(directory, fileName), "file {0} does not exist; files={1}", fileName, new Directory.ListAllFormatter(directory));
                    // If this trips it means we are missing a call to
                    // .checkpoint somewhere, because by the time we
                    // are called, deleter should know about every
                    // file referenced by the current head
                    // segmentInfos:
                    Debugging.Assert(deleter.Exists(fileName), "IndexFileDeleter doesn't know about file {0}", fileName);
                }
            }
            return true;
        }

        // For infoStream output
        internal virtual SegmentInfos ToLiveInfos(SegmentInfos sis)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                SegmentInfos newSIS = new SegmentInfos();
                IDictionary<SegmentCommitInfo, SegmentCommitInfo> liveSIS = new Dictionary<SegmentCommitInfo, SegmentCommitInfo>();
                foreach (SegmentCommitInfo info in segmentInfos.Segments)
                {
                    liveSIS[info] = info;
                }
                foreach (SegmentCommitInfo info in sis.Segments)
                {
                    SegmentCommitInfo infoMod = info;
                    if (liveSIS.TryGetValue(info, out SegmentCommitInfo liveInfo))
                    {
                        infoMod = liveInfo;
                    }
                    newSIS.Add(infoMod);
                }

                return newSIS;
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private void StartCommit(SegmentInfos toSync)
        {
            if (Debugging.AssertsEnabled)
            {
                Debugging.Assert(TestPoint("startStartCommit"));
                Debugging.Assert(pendingCommit is null);
            }

            if (hitOOM)
            {
                throw IllegalStateException.Create("this writer hit an OutOfMemoryError; cannot commit");
            }

            try
            {
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "StartCommit(): start");
                }

                UninterruptableMonitor.Enter(this);
                try
                {
                    if (Debugging.AssertsEnabled) Debugging.Assert(lastCommitChangeCount <= changeCount,"lastCommitChangeCount={0} changeCount={1}", lastCommitChangeCount, changeCount);

                    if (pendingCommitChangeCount == lastCommitChangeCount)
                    {
                        if (infoStream.IsEnabled("IW"))
                        {
                            infoStream.Message("IW", "  skip StartCommit(): no changes pending");
                        }
                        deleter.DecRef(filesToCommit);
                        filesToCommit = null;
                        return;
                    }

                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "startCommit index=" + SegString(ToLiveInfos(toSync).Segments) + " changeCount=" + changeCount);
                    }

                    if (Debugging.AssertsEnabled) Debugging.Assert(FilesExist(toSync));
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }

                if (Debugging.AssertsEnabled) Debugging.Assert(TestPoint("midStartCommit"));

                bool pendingCommitSet = false;

                try
                {
                    if (Debugging.AssertsEnabled) Debugging.Assert(TestPoint("midStartCommit2"));

                    UninterruptableMonitor.Enter(this);
                    try
                    {
                        if (Debugging.AssertsEnabled) Debugging.Assert(pendingCommit is null);

                        if (Debugging.AssertsEnabled) Debugging.Assert(segmentInfos.Generation == toSync.Generation);

                        // Exception here means nothing is prepared
                        // (this method unwinds everything it did on
                        // an exception)
                        toSync.PrepareCommit(directory);
                        //System.out.println("DONE prepareCommit");

                        pendingCommitSet = true;
                        pendingCommit = toSync;
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(this);
                    }

                    // this call can take a long time -- 10s of seconds
                    // or more.  We do it without syncing on this:
                    bool success = false;
                    ICollection<string> filesToSync;
                    try
                    {
                        filesToSync = toSync.GetFiles(directory, false);
                        directory.Sync(filesToSync);
                        success = true;
                    }
                    finally
                    {
                        if (!success)
                        {
                            pendingCommitSet = false;
                            pendingCommit = null;
                            toSync.RollbackCommit(directory);
                        }
                    }

                    if (infoStream.IsEnabled("IW"))
                    {
                        infoStream.Message("IW", "done all syncs: " + string.Format(J2N.Text.StringFormatter.InvariantCulture, "{0}", filesToSync));
                    }

                    if (Debugging.AssertsEnabled) Debugging.Assert(TestPoint("midStartCommitSuccess"));
                }
                finally
                {
                    UninterruptableMonitor.Enter(this);
                    try
                    {
                        segmentInfos.UpdateGeneration(toSync);

                        if (!pendingCommitSet)
                        {
                            if (infoStream.IsEnabled("IW"))
                            {
                                infoStream.Message("IW", "hit exception committing segments file");
                            }

                            // Hit exception
                            deleter.DecRef(filesToCommit);
                            filesToCommit = null;
                        }
                    }
                    finally
                    {
                        UninterruptableMonitor.Exit(this);
                    }
                }
            }
            catch (Exception oom) when (oom.IsOutOfMemoryError())
            {
                HandleOOM(oom, "StartCommit");
            }
            if (Debugging.AssertsEnabled) Debugging.Assert(TestPoint("finishStartCommit"));
        }

        public static bool IsLocked(Directory directory)
        {
            return directory.MakeLock(WRITE_LOCK_NAME).IsLocked();
        }

        public static void Unlock(Directory directory)
        {
            using var _ = directory.MakeLock(IndexWriter.WRITE_LOCK_NAME);
        }

        public abstract class IndexReaderWarmer
        {
            protected IndexReaderWarmer() { }

            public abstract void Warm(AtomicReader reader);
        }

        private void HandleOOM(/*OutOfMemory*/Exception oom, string location) // LUCENENET: Our handler doesn't cast to OutOfMemoryException, so we need to widen the parameter to accept Exception
        {
            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "hit OutOfMemoryError inside " + location);
            }
            hitOOM = true;
            ExceptionDispatchInfo.Capture(oom).Throw(); // LUCENENET: Rethrow to preserve stack details from the original throw
        }

        private bool TestPoint(string message)
        {
            if (infoStream.IsEnabled("TP"))
            {
                infoStream.Message("TP", message);
            }
            return true;
        }

        internal virtual bool NrtIsCurrent(SegmentInfos infos)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                EnsureOpen();
                if (infoStream.IsEnabled("IW"))
                {
                    infoStream.Message("IW", "nrtIsCurrent: infoVersion matches: " + (infos.Version == segmentInfos.Version) + "; DW changes: " + docWriter.AnyChanges() + "; BD changes: " + bufferedUpdatesStream.Any());
                }
                return infos.Version == segmentInfos.Version && !docWriter.AnyChanges() && !bufferedUpdatesStream.Any();
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        public virtual bool IsClosed
        {
            get
            {
                UninterruptableMonitor.Enter(this);
                try
                {
                    return closed;
                }
                finally
                {
                    UninterruptableMonitor.Exit(this);
                }
            }
        }

        public virtual void DeleteUnusedFiles()
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                EnsureOpen(false);
                deleter.DeletePendingFiles();
                deleter.RevisitPolicy();
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        internal static ICollection<string> CreateCompoundFile(InfoStream infoStream, Directory directory, CheckAbort checkAbort, SegmentInfo info, IOContext context)
        {
            string fileName = Index.IndexFileNames.SegmentFileName(info.Name, "", Lucene.Net.Index.IndexFileNames.COMPOUND_FILE_EXTENSION);
            if (infoStream.IsEnabled("IW"))
            {
                infoStream.Message("IW", "create compound file " + fileName);
            }
            if (Debugging.AssertsEnabled) Debugging.Assert(Lucene3xSegmentInfoFormat.GetDocStoreOffset(info) == -1);
            // Now merge all added files
            ICollection<string> files = info.GetFiles();
            CompoundFileDirectory cfsDir = new CompoundFileDirectory(directory, fileName, context, true);
            // LUCENENET: Ported changes to this method from 4.8.1
            bool success = false;
            try
            {
                foreach (string file in files)
                {
                    directory.Copy(cfsDir, file, file, context);
                    checkAbort.Work(directory.FileLength(file));
                }
                success = true;
            }
            finally
            {
                if (success)
                {
                    IOUtils.Dispose(cfsDir);
                }
                else
                {
                    IOUtils.DisposeWhileHandlingException(cfsDir);
                    try
                    {
                        directory.DeleteFile(fileName);
                    }
                    catch (Exception t) when (t.IsThrowable())
                    {
                    }
                    try
                    {
                        directory.DeleteFile(Lucene.Net.Index.IndexFileNames.SegmentFileName(info.Name, "", Lucene.Net.Index.IndexFileNames.COMPOUND_FILE_ENTRIES_EXTENSION));
                    }
                    catch (Exception t) when (t.IsThrowable())
                    {
                    }
                }
            }

            // Replace all previous files with the CFS/CFE files:
            JCG.HashSet<string> siFiles = new JCG.HashSet<string>
            {
                fileName,
                Lucene.Net.Index.IndexFileNames.SegmentFileName(info.Name, "", Lucene.Net.Index.IndexFileNames.COMPOUND_FILE_ENTRIES_EXTENSION)
            };
            info.SetFiles(siFiles);

            return files;
        }

        internal void DeleteNewFiles(ICollection<string> files)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                deleter.DeleteNewFiles(files);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        internal void FlushFailed(SegmentInfo info)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                deleter.Refresh(info.Name);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        internal int Purge(bool forced)
        {
            return docWriter.PurgeBuffer(this, forced);
        }

        internal void ApplyDeletesAndPurge(bool forcePurge)
        {
            try
            {
                Purge(forcePurge);
            }
            finally
            {
                ApplyAllDeletesAndUpdates();
                flushCount.IncrementAndGet();
            }
        }

        internal void DoAfterSegmentFlushed(bool triggerMerge, bool forcePurge)
        {
            try
            {
                Purge(forcePurge);
            }
            finally
            {
                if (triggerMerge)
                {
                    MaybeMerge(MergeTrigger.SEGMENT_FLUSH, UNBOUNDED_MAX_MERGE_SEGMENTS);
                }
            }
        }

        internal virtual void IncRefDeleter(SegmentInfos segmentInfos)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                EnsureOpen();
                deleter.IncRef(segmentInfos, false);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        internal virtual void DecRefDeleter(SegmentInfos segmentInfos)
        {
            UninterruptableMonitor.Enter(this);
            try
            {
                EnsureOpen();
                deleter.DecRef(segmentInfos);
            }
            finally
            {
                UninterruptableMonitor.Exit(this);
            }
        }

        private bool ProcessEvents(bool triggerMerge, bool forcePurge)
        {
            return ProcessEvents(eventQueue, triggerMerge, forcePurge);
        }

        private bool ProcessEvents(ConcurrentQueue<IEvent> queue, bool triggerMerge, bool forcePurge)
        {
            bool processed = false;
            while (queue.TryDequeue(out IEvent @event))
            {
                processed = true;
                @event.Process(this, triggerMerge, forcePurge);
            }
            return processed;
        }

        internal interface IEvent
        {
            void Process(IndexWriter writer, bool triggerMerge, bool clearBuffers);
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private static bool SlowFileExists(Directory dir, string fileName)
        {
            try
            {
                using (var input = dir.OpenInput(fileName, IOContext.DEFAULT)) { }
                return true;
            }
            catch (Exception e) when (e.IsNoSuchFileExceptionOrFileNotFoundException())
            {
                return false;
            }
        }
    }
}