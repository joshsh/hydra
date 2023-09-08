package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Enum to annotate whether lists of min/max elements inside ColumnIndex are ordered and if so, in which direction.
 */
public abstract class BoundaryOrder implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.BoundaryOrder");
  
  private BoundaryOrder () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Unordered instance) ;
    
    R visit(Ascending instance) ;
    
    R visit(Descending instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(BoundaryOrder instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Unordered instance) {
      return otherwise((instance));
    }
    
    default R visit(Ascending instance) {
      return otherwise((instance));
    }
    
    default R visit(Descending instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Unordered extends hydra.langs.parquet.format.BoundaryOrder implements Serializable {
    public Unordered () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Unordered)) {
        return false;
      }
      Unordered o = (Unordered) (other);
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
  
  public static final class Ascending extends hydra.langs.parquet.format.BoundaryOrder implements Serializable {
    public Ascending () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Ascending)) {
        return false;
      }
      Ascending o = (Ascending) (other);
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
  
  public static final class Descending extends hydra.langs.parquet.format.BoundaryOrder implements Serializable {
    public Descending () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Descending)) {
        return false;
      }
      Descending o = (Descending) (other);
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