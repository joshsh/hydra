package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Timestamp logical type annotation. Allowed for physical types: INT64
 */
public class TimestampType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.TimestampType");
  
  public final Boolean isAdjustedToUtc;
  
  public final hydra.langs.parquet.format.TimeUnit unit;
  
  public TimestampType (Boolean isAdjustedToUtc, hydra.langs.parquet.format.TimeUnit unit) {
    this.isAdjustedToUtc = isAdjustedToUtc;
    this.unit = unit;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TimestampType)) {
      return false;
    }
    TimestampType o = (TimestampType) (other);
    return isAdjustedToUtc.equals(o.isAdjustedToUtc) && unit.equals(o.unit);
  }
  
  @Override
  public int hashCode() {
    return 2 * isAdjustedToUtc.hashCode() + 3 * unit.hashCode();
  }
  
  public TimestampType withIsAdjustedToUtc(Boolean isAdjustedToUtc) {
    return new TimestampType(isAdjustedToUtc, unit);
  }
  
  public TimestampType withUnit(hydra.langs.parquet.format.TimeUnit unit) {
    return new TimestampType(isAdjustedToUtc, unit);
  }
}