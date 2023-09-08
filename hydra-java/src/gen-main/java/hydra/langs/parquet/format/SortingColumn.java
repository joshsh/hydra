package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Wrapper struct to specify sort order
 */
public class SortingColumn implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.SortingColumn");
  
  /**
   * The column index (in this row group)
   */
  public final Integer columnIdx;
  
  /**
   * If true, indicates this column is sorted in descending order.
   */
  public final Boolean descending;
  
  /**
   * If true, nulls will come before non-null values, otherwise, nulls go at the end.
   */
  public final Boolean nullsFirst;
  
  public SortingColumn (Integer columnIdx, Boolean descending, Boolean nullsFirst) {
    this.columnIdx = columnIdx;
    this.descending = descending;
    this.nullsFirst = nullsFirst;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SortingColumn)) {
      return false;
    }
    SortingColumn o = (SortingColumn) (other);
    return columnIdx.equals(o.columnIdx) && descending.equals(o.descending) && nullsFirst.equals(o.nullsFirst);
  }
  
  @Override
  public int hashCode() {
    return 2 * columnIdx.hashCode() + 3 * descending.hashCode() + 5 * nullsFirst.hashCode();
  }
  
  public SortingColumn withColumnIdx(Integer columnIdx) {
    return new SortingColumn(columnIdx, descending, nullsFirst);
  }
  
  public SortingColumn withDescending(Boolean descending) {
    return new SortingColumn(columnIdx, descending, nullsFirst);
  }
  
  public SortingColumn withNullsFirst(Boolean nullsFirst) {
    return new SortingColumn(columnIdx, descending, nullsFirst);
  }
}