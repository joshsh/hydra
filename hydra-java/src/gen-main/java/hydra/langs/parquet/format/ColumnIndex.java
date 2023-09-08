package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Description for ColumnIndex. Each &lt;array-field&gt;[i] refers to the page at OffsetIndex.page_locations[i]
 */
public class ColumnIndex implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.ColumnIndex");
  
  /**
   * A list of Boolean values to determine the validity of the corresponding min and max values. If true, a page contains only null values, and writers have to set the corresponding entries in min_values and max_values to byte[0], so that all lists have the same length. If false, the corresponding entries in min_values and max_values must be valid.
   */
  public final java.util.List<Boolean> nullPages;
  
  public final java.util.List<String> minValues;
  
  public final java.util.List<String> maxValues;
  
  /**
   * Stores whether both min_values and max_values are orderd and if so, in which direction. This allows readers to perform binary searches in both lists. Readers cannot assume that max_values[i] &lt;= min_values[i+1], even if the lists are ordered.
   */
  public final hydra.langs.parquet.format.BoundaryOrder boundaryOrder;
  
  /**
   * A list containing the number of null values for each page
   */
  public final java.util.Optional<java.util.List<Long>> nullCounts;
  
  public ColumnIndex (java.util.List<Boolean> nullPages, java.util.List<String> minValues, java.util.List<String> maxValues, hydra.langs.parquet.format.BoundaryOrder boundaryOrder, java.util.Optional<java.util.List<Long>> nullCounts) {
    this.nullPages = nullPages;
    this.minValues = minValues;
    this.maxValues = maxValues;
    this.boundaryOrder = boundaryOrder;
    this.nullCounts = nullCounts;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnIndex)) {
      return false;
    }
    ColumnIndex o = (ColumnIndex) (other);
    return nullPages.equals(o.nullPages) && minValues.equals(o.minValues) && maxValues.equals(o.maxValues) && boundaryOrder.equals(o.boundaryOrder) && nullCounts.equals(o.nullCounts);
  }
  
  @Override
  public int hashCode() {
    return 2 * nullPages.hashCode() + 3 * minValues.hashCode() + 5 * maxValues.hashCode() + 7 * boundaryOrder.hashCode() + 11 * nullCounts.hashCode();
  }
  
  public ColumnIndex withNullPages(java.util.List<Boolean> nullPages) {
    return new ColumnIndex(nullPages, minValues, maxValues, boundaryOrder, nullCounts);
  }
  
  public ColumnIndex withMinValues(java.util.List<String> minValues) {
    return new ColumnIndex(nullPages, minValues, maxValues, boundaryOrder, nullCounts);
  }
  
  public ColumnIndex withMaxValues(java.util.List<String> maxValues) {
    return new ColumnIndex(nullPages, minValues, maxValues, boundaryOrder, nullCounts);
  }
  
  public ColumnIndex withBoundaryOrder(hydra.langs.parquet.format.BoundaryOrder boundaryOrder) {
    return new ColumnIndex(nullPages, minValues, maxValues, boundaryOrder, nullCounts);
  }
  
  public ColumnIndex withNullCounts(java.util.Optional<java.util.List<Long>> nullCounts) {
    return new ColumnIndex(nullPages, minValues, maxValues, boundaryOrder, nullCounts);
  }
}