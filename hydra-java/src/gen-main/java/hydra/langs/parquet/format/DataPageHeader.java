package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Data page header
 */
public class DataPageHeader implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.DataPageHeader");
  
  /**
   * Number of values, including NULLs, in this data page.
   */
  public final Integer numValues;
  
  /**
   * Encoding used for this data page
   */
  public final hydra.langs.parquet.format.Encoding encoding;
  
  /**
   * Encoding used for definition levels
   */
  public final hydra.langs.parquet.format.Encoding definitionLevelEncoding;
  
  /**
   * Encoding used for repetition levels
   */
  public final hydra.langs.parquet.format.Encoding repetitionLevelEncoding;
  
  /**
   * Optional statistics for the data in this page
   */
  public final java.util.Optional<hydra.langs.parquet.format.Statistics> statistics;
  
  public DataPageHeader (Integer numValues, hydra.langs.parquet.format.Encoding encoding, hydra.langs.parquet.format.Encoding definitionLevelEncoding, hydra.langs.parquet.format.Encoding repetitionLevelEncoding, java.util.Optional<hydra.langs.parquet.format.Statistics> statistics) {
    this.numValues = numValues;
    this.encoding = encoding;
    this.definitionLevelEncoding = definitionLevelEncoding;
    this.repetitionLevelEncoding = repetitionLevelEncoding;
    this.statistics = statistics;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataPageHeader)) {
      return false;
    }
    DataPageHeader o = (DataPageHeader) (other);
    return numValues.equals(o.numValues) && encoding.equals(o.encoding) && definitionLevelEncoding.equals(o.definitionLevelEncoding) && repetitionLevelEncoding.equals(o.repetitionLevelEncoding) && statistics.equals(o.statistics);
  }
  
  @Override
  public int hashCode() {
    return 2 * numValues.hashCode() + 3 * encoding.hashCode() + 5 * definitionLevelEncoding.hashCode() + 7 * repetitionLevelEncoding.hashCode() + 11 * statistics.hashCode();
  }
  
  public DataPageHeader withNumValues(Integer numValues) {
    return new DataPageHeader(numValues, encoding, definitionLevelEncoding, repetitionLevelEncoding, statistics);
  }
  
  public DataPageHeader withEncoding(hydra.langs.parquet.format.Encoding encoding) {
    return new DataPageHeader(numValues, encoding, definitionLevelEncoding, repetitionLevelEncoding, statistics);
  }
  
  public DataPageHeader withDefinitionLevelEncoding(hydra.langs.parquet.format.Encoding definitionLevelEncoding) {
    return new DataPageHeader(numValues, encoding, definitionLevelEncoding, repetitionLevelEncoding, statistics);
  }
  
  public DataPageHeader withRepetitionLevelEncoding(hydra.langs.parquet.format.Encoding repetitionLevelEncoding) {
    return new DataPageHeader(numValues, encoding, definitionLevelEncoding, repetitionLevelEncoding, statistics);
  }
  
  public DataPageHeader withStatistics(java.util.Optional<hydra.langs.parquet.format.Statistics> statistics) {
    return new DataPageHeader(numValues, encoding, definitionLevelEncoding, repetitionLevelEncoding, statistics);
  }
}