// Note: this is an automatically generated file. Do not edit.

package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * The dictionary page must be placed at the first position of the column chunk if it is partly or completely dictionary encoded. At most one dictionary page can be placed in a column chunk.
 */
public class DictionaryPageHeader implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.DictionaryPageHeader");
  
  /**
   * Number of values in the dictionary
   */
  public final Integer numValues;
  
  /**
   * Encoding using this dictionary page
   */
  public final hydra.langs.parquet.format.Encoding encoding;
  
  /**
   * If true, the entries in the dictionary are sorted in ascending order
   */
  public final hydra.util.Opt<Boolean> isSorted;
  
  public DictionaryPageHeader (Integer numValues, hydra.langs.parquet.format.Encoding encoding, hydra.util.Opt<Boolean> isSorted) {
    if (numValues == null) {
      throw new IllegalArgumentException("null value for 'numValues' argument");
    }
    if (encoding == null) {
      throw new IllegalArgumentException("null value for 'encoding' argument");
    }
    if (isSorted == null) {
      throw new IllegalArgumentException("null value for 'isSorted' argument");
    }
    this.numValues = numValues;
    this.encoding = encoding;
    this.isSorted = isSorted;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DictionaryPageHeader)) {
      return false;
    }
    DictionaryPageHeader o = (DictionaryPageHeader) (other);
    return numValues.equals(o.numValues) && encoding.equals(o.encoding) && isSorted.equals(o.isSorted);
  }
  
  @Override
  public int hashCode() {
    return 2 * numValues.hashCode() + 3 * encoding.hashCode() + 5 * isSorted.hashCode();
  }
  
  public DictionaryPageHeader withNumValues(Integer numValues) {
    if (numValues == null) {
      throw new IllegalArgumentException("null value for 'numValues' argument");
    }
    return new DictionaryPageHeader(numValues, encoding, isSorted);
  }
  
  public DictionaryPageHeader withEncoding(hydra.langs.parquet.format.Encoding encoding) {
    if (encoding == null) {
      throw new IllegalArgumentException("null value for 'encoding' argument");
    }
    return new DictionaryPageHeader(numValues, encoding, isSorted);
  }
  
  public DictionaryPageHeader withIsSorted(hydra.util.Opt<Boolean> isSorted) {
    if (isSorted == null) {
      throw new IllegalArgumentException("null value for 'isSorted' argument");
    }
    return new DictionaryPageHeader(numValues, encoding, isSorted);
  }
}