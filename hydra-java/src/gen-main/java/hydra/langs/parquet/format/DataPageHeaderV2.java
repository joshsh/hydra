package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * New page format allowing reading levels without decompressing the data Repetition and definition levels are uncompressed The remaining section containing the data is compressed if is_compressed is true
 */
public class DataPageHeaderV2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.DataPageHeaderV2");
  
  /**
   * Number of values, including NULLs, in this data page.
   */
  public final Integer numValues;
  
  /**
   * Number of NULL values, in this data page. Number of non-null = num_values - num_nulls which is also the number of values in the data section
   */
  public final Integer numNulls;
  
  /**
   * Number of rows in this data page. which means pages change on record boundaries (r = 0)
   */
  public final Integer numRows;
  
  /**
   * Encoding used for data in this page
   */
  public final hydra.langs.parquet.format.Encoding encoding;
  
  /**
   * length of the definition levels
   */
  public final Integer definitionLevelsByteLength;
  
  /**
   * length of the repetition levels
   */
  public final Integer repetitionLevelsByteLength;
  
  /**
   * whether the values are compressed. Which means the section of the page between definition_levels_byte_length + repetition_levels_byte_length + 1 and compressed_page_size (included) is compressed with the compression_codec. If missing it is considered compressed
   */
  public final java.util.Optional<Boolean> isCompressed;
  
  /**
   * optional statistics for the data in this page
   */
  public final java.util.Optional<hydra.langs.parquet.format.Statistics> statistics;
  
  public DataPageHeaderV2 (Integer numValues, Integer numNulls, Integer numRows, hydra.langs.parquet.format.Encoding encoding, Integer definitionLevelsByteLength, Integer repetitionLevelsByteLength, java.util.Optional<Boolean> isCompressed, java.util.Optional<hydra.langs.parquet.format.Statistics> statistics) {
    this.numValues = numValues;
    this.numNulls = numNulls;
    this.numRows = numRows;
    this.encoding = encoding;
    this.definitionLevelsByteLength = definitionLevelsByteLength;
    this.repetitionLevelsByteLength = repetitionLevelsByteLength;
    this.isCompressed = isCompressed;
    this.statistics = statistics;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataPageHeaderV2)) {
      return false;
    }
    DataPageHeaderV2 o = (DataPageHeaderV2) (other);
    return numValues.equals(o.numValues) && numNulls.equals(o.numNulls) && numRows.equals(o.numRows) && encoding.equals(o.encoding) && definitionLevelsByteLength.equals(o.definitionLevelsByteLength) && repetitionLevelsByteLength.equals(o.repetitionLevelsByteLength) && isCompressed.equals(o.isCompressed) && statistics.equals(o.statistics);
  }
  
  @Override
  public int hashCode() {
    return 2 * numValues.hashCode() + 3 * numNulls.hashCode() + 5 * numRows.hashCode() + 7 * encoding.hashCode() + 11 * definitionLevelsByteLength.hashCode() + 13 * repetitionLevelsByteLength.hashCode() + 17 * isCompressed.hashCode() + 19 * statistics.hashCode();
  }
  
  public DataPageHeaderV2 withNumValues(Integer numValues) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
  
  public DataPageHeaderV2 withNumNulls(Integer numNulls) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
  
  public DataPageHeaderV2 withNumRows(Integer numRows) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
  
  public DataPageHeaderV2 withEncoding(hydra.langs.parquet.format.Encoding encoding) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
  
  public DataPageHeaderV2 withDefinitionLevelsByteLength(Integer definitionLevelsByteLength) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
  
  public DataPageHeaderV2 withRepetitionLevelsByteLength(Integer repetitionLevelsByteLength) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
  
  public DataPageHeaderV2 withIsCompressed(java.util.Optional<Boolean> isCompressed) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
  
  public DataPageHeaderV2 withStatistics(java.util.Optional<hydra.langs.parquet.format.Statistics> statistics) {
    return new DataPageHeaderV2(numValues, numNulls, numRows, encoding, definitionLevelsByteLength, repetitionLevelsByteLength, isCompressed, statistics);
  }
}