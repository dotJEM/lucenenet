using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Diagnostics.dotTrace;
using BenchmarkDotNet.Jobs;
using BenchmarkDotNet.Running;
using Lucene.Net.Analysis.Standard;
using Lucene.Net.Documents;
using Lucene.Net.Facet;
using Lucene.Net.Facet.Taxonomy;
using Lucene.Net.Facet.Taxonomy.Directory;
using Lucene.Net.Index;
using Lucene.Net.Search;
using Lucene.Net.Store;
using Lucene.Net.Support;
using Lucene.Net.Util;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics.Arm;
using Directory = System.IO.Directory;
using IOException = System.IO.IOException;
using ObjectDisposedException = System.ObjectDisposedException;

BenchmarkRunner.Run<LuceneBenchmarks>(
//    new DebugBuildConfig()
    );

[SimpleJob(RuntimeMoniker.Net70, baseline: true)]
[SimpleJob(RuntimeMoniker.Net80)]
[RPlotExporter]
[GcServer(true)]
[DotTraceDiagnoser]
public class LuceneBenchmarks
{
    private DirectoryTaxonomyWriter taxonomyWriter;
    private IndexWriter indexWriter;
    private Document[] documents;
    private FacetsConfig facetsConfig;
    private SearcherTaxonomyManager searcherManager;

    [GlobalSetup]
    public void Setup()
    {
        if (Directory.Exists("test_index"))
        {
            Directory.Delete("test_index", true);
        }

        if (Directory.Exists("test_facets"))
        {
            Directory.Delete("test_facets", true);
        }

        var analyzer = new StandardAnalyzer(LuceneVersion.LUCENE_48);
        var luceneDirectory = new CustomMMapDirectory("test_index");
        indexWriter = new IndexWriter(luceneDirectory, new IndexWriterConfig(LuceneVersion.LUCENE_48, analyzer));
        taxonomyWriter = new DirectoryTaxonomyWriter(new CustomMMapDirectory("test_facets"));
        facetsConfig = new FacetsConfig();
        searcherManager = new SearcherTaxonomyManager(indexWriter, true, new SearcherFactory(), taxonomyWriter);
        facetsConfig.SetRequireDimCount("track_id", true);

        documents = new Document[N];
        for (int i = 0; i < N; i++)
        {
            var facet = GenerateRandomString(5);
            documents[i] = new Document
            {
                new StringField("_id", i.ToString(), Field.Store.YES),
                new TextField("content", GenerateRandomString(10), Field.Store.YES),
                new FacetField("track_id", facet)
            };
        }
    }

    [Params(100)]
    public int N;

    [Benchmark]
    public int IndexDocumentsBenchmark() => IndexDocuments();

    private int IndexDocuments()
    {
        for (int i = 0; i < documents.Length; ++i)
        {
            var taxonomyDocument = facetsConfig.Build(taxonomyWriter, documents[i]);
            indexWriter.UpdateDocument(new Term("_id", i.ToString()), taxonomyDocument);
            searcherManager.MaybeRefresh(); // maybe refresh causing dramatic performance drop on .NET 8.0
        }

        return documents.Length;
    }

    private static string GenerateRandomString(int length)
    {
        // more spaces added on purpose
        const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789         ";
        char[] stringChars = new char[length];

        for (int i = 0; i < length; i++)
        {
            stringChars[i] = chars[Random.Shared.Next(chars.Length)];
        }

        return new string(stringChars);
    }
}

public class CustomMMapDirectory : MMapDirectory
{
    public CustomMMapDirectory(DirectoryInfo path, LockFactory lockFactory) : base(path, lockFactory)
    {
    }

    public CustomMMapDirectory(DirectoryInfo path) : base(path)
    {
    }

    public CustomMMapDirectory(DirectoryInfo path, LockFactory lockFactory, int maxChunkSize) : base(path, lockFactory, maxChunkSize)
    {
    }

    public CustomMMapDirectory(string path, LockFactory lockFactory) : base(path, lockFactory)
    {
    }

    public CustomMMapDirectory(string path) : base(path)
    {
    }

    public CustomMMapDirectory(string path, LockFactory lockFactory, int maxChunkSize) : base(path, lockFactory, maxChunkSize)
    {
    }

    public override IndexOutput CreateOutput(string name, IOContext context)
    {
        EnsureOpen();

        EnsureCanWrite(name);
        return new CustomFSIndexOutput(this, name);
    }

    protected class CustomFSIndexOutput : IndexOutput
    {
        private readonly CustomMMapDirectory directory;
        public const int DEFAULT_BUFFER_SIZE = 16384;
        private const int CHUNK_SIZE = DEFAULT_BUFFER_SIZE;
        internal readonly string name;

        private readonly CRC32 crc = new CRC32();
        private readonly FileStream file;
        private volatile bool isOpen; // remember if the file is open, so that we don't try to close it more than once

        public override long Length => file.Length;
        public override long Position => file.Position;

        public override long Checksum => crc.Value;

        public CustomFSIndexOutput(CustomMMapDirectory directory, string name)
        {
            this.directory = directory;
            this.name = name;
            file = new FileStream(
                path: Path.Combine(this.directory.m_directory.FullName, name),
                mode: FileMode.OpenOrCreate,
                access: FileAccess.Write,
                share: FileShare.ReadWrite,
                bufferSize: CHUNK_SIZE);
            isOpen = true;
        }


        public override void WriteByte(byte b)
        {
            CheckDisposed();

            crc.Update(b);
            file.WriteByte(b);
        }

        public override void WriteBytes(byte[] b, int offset, int length)
        {
            CheckDisposed();

            crc.Update(b, offset, length);
            file.Write(b, offset, length);
        }

        public override void Flush()
        {
            CheckDisposed();
            file.Flush();
        }

        protected override void Dispose(bool disposing)
        {
            if (!disposing) return;

            //Method is empty
            //parent.OnIndexOutputClosed(this);
            if (!isOpen) return;

            Exception priorE = null; 
            try
            {
                file.Flush(flushToDisk: false);
            }
            catch (Exception ioe) when (ioe is IOException or UnauthorizedAccessException or ObjectDisposedException)
            {
                priorE = ioe;
            }
            finally
            {
                isOpen = false;
                IOUtils.DisposeWhileHandlingException(priorE, file);
            }
        }

        public override void Seek(long pos)
        {
            CheckDisposed();

            file.Seek(pos, SeekOrigin.Begin);
        }

        private void CheckDisposed()
        {
            if (!isOpen)
                throw new ObjectDisposedException("");
        }
    }
}