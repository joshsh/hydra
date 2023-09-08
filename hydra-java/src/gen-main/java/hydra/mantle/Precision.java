package hydra.mantle;

import java.io.Serializable;

/**
 * Numeric precision: arbitrary precision, or precision to a specified number of bits
 */
public abstract class Precision implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/mantle.Precision");
  
  private Precision () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Arbitrary instance) ;
    
    R visit(Bits instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Precision instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Arbitrary instance) {
      return otherwise((instance));
    }
    
    default R visit(Bits instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Arbitrary extends hydra.mantle.Precision implements Serializable {
    public Arbitrary () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Arbitrary)) {
        return false;
      }
      Arbitrary o = (Arbitrary) (other);
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
  
  public static final class Bits extends hydra.mantle.Precision implements Serializable {
    public final Integer value;
    
    public Bits (Integer value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Bits)) {
        return false;
      }
      Bits o = (Bits) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
}