package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Union to specify the order used for the min_value and max_value fields for a column. This union takes the role of an enhanced enum that allows rich elements (which will be needed for a collation-based ordering in the future). Possible values are:
 * * TypeDefinedOrder - the column uses the order defined by its logical or physical type (if there is no logical type).
 * If the reader does not support the value of this union, min and max stats for this column should be ignored. 
 */
public abstract class ColumnOrder implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.ColumnOrder");
  
  private ColumnOrder () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(TypeOrder instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ColumnOrder instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(TypeOrder instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * The sort orders for logical types are:
   *   UTF8 - unsigned byte-wise comparison
   *   INT8 - signed comparison
   *   INT16 - signed comparison
   *   INT32 - signed comparison
   *   INT64 - signed comparison
   *   UINT8 - unsigned comparison
   *   UINT16 - unsigned comparison
   *   UINT32 - unsigned comparison
   *   UINT64 - unsigned comparison
   *   DECIMAL - signed comparison of the represented value
   *   DATE - signed comparison
   *   TIME_MILLIS - signed comparison
   *   TIME_MICROS - signed comparison
   *   TIMESTAMP_MILLIS - signed comparison
   *   TIMESTAMP_MICROS - signed comparison
   *   INTERVAL - unsigned comparison
   *   JSON - unsigned byte-wise comparison
   *   BSON - unsigned byte-wise comparison
   *   ENUM - unsigned byte-wise comparison
   *   LIST - undefined
   *   MAP - undefined
   * In the absence of logical types, the sort order is determined by the physical type:
   *   BOOLEAN - false, true
   *   INT32 - signed comparison
   *   INT64 - signed comparison
   *   INT96 (only used for legacy timestamps) - undefined
   *   FLOAT - signed comparison of the represented value (*)
   *   DOUBLE - signed comparison of the represented value (*)
   *   BYTE_ARRAY - unsigned byte-wise comparison
   *   FIXED_LEN_BYTE_ARRAY - unsigned byte-wise comparison
   * (*) Because the sorting order is not specified properly for floating
   *     point values (relations vs. total ordering) the following
   *     compatibility rules should be applied when reading statistics:
   *     - If the min is a NaN, it should be ignored.
   *     - If the max is a NaN, it should be ignored.
   *     - If the min is +0, the row group may contain -0 values as well.
   *     - If the max is -0, the row group may contain +0 values as well.
   *     - When looking for NaN values, min and max should be ignored.
   */
  public static final class TypeOrder extends hydra.langs.parquet.format.ColumnOrder implements Serializable {
    public TypeOrder () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof TypeOrder)) {
        return false;
      }
      TypeOrder o = (TypeOrder) (other);
      return true;
    }
    
    @Override
    public int hashCode() {
      return 0;
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
}