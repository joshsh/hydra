package hydra.langs.parquet.format;

import java.io.Serializable;

public class OffsetIndex implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.OffsetIndex");
  
  /**
   * PageLocations, ordered by increasing PageLocation.offset. It is required that page_locations[i].first_row_index &lt; page_locations[i+1].first_row_index.
   */
  public final java.util.List<hydra.langs.parquet.format.PageLocation> pageLocations;
  
  public OffsetIndex (java.util.List<hydra.langs.parquet.format.PageLocation> pageLocations) {
    this.pageLocations = pageLocations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof OffsetIndex)) {
      return false;
    }
    OffsetIndex o = (OffsetIndex) (other);
    return pageLocations.equals(o.pageLocations);
  }
  
  @Override
  public int hashCode() {
    return 2 * pageLocations.hashCode();
  }
}