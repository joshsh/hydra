package hydra.coders;

import java.io.Serializable;

/**
 * Indicates either the 'out' or the 'in' direction of a coder
 */
public abstract class CoderDirection implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/coders.CoderDirection");
  
  private CoderDirection () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Encode instance) ;
    
    R visit(Decode instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(CoderDirection instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Encode instance) {
      return otherwise((instance));
    }
    
    default R visit(Decode instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Encode extends hydra.coders.CoderDirection implements Serializable {
    public Encode () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Encode)) {
        return false;
      }
      Encode o = (Encode) (other);
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
  
  public static final class Decode extends hydra.coders.CoderDirection implements Serializable {
    public Decode () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Decode)) {
        return false;
      }
      Decode o = (Decode) (other);
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