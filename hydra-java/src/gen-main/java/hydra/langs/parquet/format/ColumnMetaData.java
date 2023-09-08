package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Description for column metadata
 */
public class ColumnMetaData implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.ColumnMetaData");
  
  /**
   * Type of this column
   */
  public final hydra.langs.parquet.format.Type type;
  
  /**
   * Set of all encodings used for this column. The purpose is to validate whether we can decode those pages.
   */
  public final java.util.List<hydra.langs.parquet.format.Encoding> encodings;
  
  /**
   * Path in schema
   */
  public final java.util.List<String> pathInSchema;
  
  /**
   * Compression codec
   */
  public final hydra.langs.parquet.format.CompressionCodec codec;
  
  /**
   * Number of values in this column
   */
  public final Long numValues;
  
  /**
   * total byte size of all uncompressed pages in this column chunk (including the headers)
   */
  public final Long totalUncompressedSize;
  
  /**
   * total byte size of all compressed, and potentially encrypted, pages in this column chunk (including the headers)
   */
  public final Long totalCompressedSize;
  
  /**
   * Optional key/value metadata
   */
  public final java.util.Optional<java.util.List<hydra.langs.parquet.format.KeyValue>> keyValueMetadata;
  
  /**
   * Byte offset from beginning of file to first data page
   */
  public final Long dataPageOffset;
  
  /**
   * Byte offset from beginning of file to root index page
   */
  public final java.util.Optional<Long> indexPageOffset;
  
  /**
   * Byte offset from the beginning of file to first (only) dictionary page
   */
  public final java.util.Optional<Long> dictionaryPageOffset;
  
  /**
   * optional statistics for this column chunk
   */
  public final java.util.Optional<hydra.langs.parquet.format.Statistics> statistics;
  
  /**
   * Set of all encodings used for pages in this column chunk. This information can be used to determine if all data pages are dictionary encoded for example
   */
  public final java.util.Optional<java.util.List<hydra.langs.parquet.format.PageEncodingStats>> encodingStats;
  
  /**
   * Byte offset from beginning of file to Bloom filter data.
   */
  public final java.util.Optional<Long> bloomFilterOffset;
  
  public ColumnMetaData (hydra.langs.parquet.format.Type type, java.util.List<hydra.langs.parquet.format.Encoding> encodings, java.util.List<String> pathInSchema, hydra.langs.parquet.format.CompressionCodec codec, Long numValues, Long totalUncompressedSize, Long totalCompressedSize, java.util.Optional<java.util.List<hydra.langs.parquet.format.KeyValue>> keyValueMetadata, Long dataPageOffset, java.util.Optional<Long> indexPageOffset, java.util.Optional<Long> dictionaryPageOffset, java.util.Optional<hydra.langs.parquet.format.Statistics> statistics, java.util.Optional<java.util.List<hydra.langs.parquet.format.PageEncodingStats>> encodingStats, java.util.Optional<Long> bloomFilterOffset) {
    this.type = type;
    this.encodings = encodings;
    this.pathInSchema = pathInSchema;
    this.codec = codec;
    this.numValues = numValues;
    this.totalUncompressedSize = totalUncompressedSize;
    this.totalCompressedSize = totalCompressedSize;
    this.keyValueMetadata = keyValueMetadata;
    this.dataPageOffset = dataPageOffset;
    this.indexPageOffset = indexPageOffset;
    this.dictionaryPageOffset = dictionaryPageOffset;
    this.statistics = statistics;
    this.encodingStats = encodingStats;
    this.bloomFilterOffset = bloomFilterOffset;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnMetaData)) {
      return false;
    }
    ColumnMetaData o = (ColumnMetaData) (other);
    return type.equals(o.type) && encodings.equals(o.encodings) && pathInSchema.equals(o.pathInSchema) && codec.equals(o.codec) && numValues.equals(o.numValues) && totalUncompressedSize.equals(o.totalUncompressedSize) && totalCompressedSize.equals(o.totalCompressedSize) && keyValueMetadata.equals(o.keyValueMetadata) && dataPageOffset.equals(o.dataPageOffset) && indexPageOffset.equals(o.indexPageOffset) && dictionaryPageOffset.equals(o.dictionaryPageOffset) && statistics.equals(o.statistics) && encodingStats.equals(o.encodingStats) && bloomFilterOffset.equals(o.bloomFilterOffset);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * encodings.hashCode() + 5 * pathInSchema.hashCode() + 7 * codec.hashCode() + 11 * numValues.hashCode() + 13 * totalUncompressedSize.hashCode() + 17 * totalCompressedSize.hashCode() + 19 * keyValueMetadata.hashCode() + 23 * dataPageOffset.hashCode() + 29 * indexPageOffset.hashCode() + 31 * dictionaryPageOffset.hashCode() + 37 * statistics.hashCode() + 41 * encodingStats.hashCode() + 43 * bloomFilterOffset.hashCode();
  }
  
  public ColumnMetaData withType(hydra.langs.parquet.format.Type type) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withEncodings(java.util.List<hydra.langs.parquet.format.Encoding> encodings) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withPathInSchema(java.util.List<String> pathInSchema) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withCodec(hydra.langs.parquet.format.CompressionCodec codec) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withNumValues(Long numValues) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withTotalUncompressedSize(Long totalUncompressedSize) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withTotalCompressedSize(Long totalCompressedSize) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withKeyValueMetadata(java.util.Optional<java.util.List<hydra.langs.parquet.format.KeyValue>> keyValueMetadata) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withDataPageOffset(Long dataPageOffset) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withIndexPageOffset(java.util.Optional<Long> indexPageOffset) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withDictionaryPageOffset(java.util.Optional<Long> dictionaryPageOffset) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withStatistics(java.util.Optional<hydra.langs.parquet.format.Statistics> statistics) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withEncodingStats(java.util.Optional<java.util.List<hydra.langs.parquet.format.PageEncodingStats>> encodingStats) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
  
  public ColumnMetaData withBloomFilterOffset(java.util.Optional<Long> bloomFilterOffset) {
    return new ColumnMetaData(type, encodings, pathInSchema, codec, numValues, totalUncompressedSize, totalCompressedSize, keyValueMetadata, dataPageOffset, indexPageOffset, dictionaryPageOffset, statistics, encodingStats, bloomFilterOffset);
  }
}