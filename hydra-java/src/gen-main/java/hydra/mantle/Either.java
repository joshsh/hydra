package hydra.mantle;

import java.io.Serializable;

/**
 * A disjoint union between a 'left' type and a 'right' type
 */
public abstract class Either<A, B> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/mantle.Either");
  
  private Either () {
  
  }
  
  public abstract <R> R accept(Visitor<A, B, R> visitor) ;
  
  public interface Visitor<A, B, R> {
    R visit(Left<A, B> instance) ;
    
    R visit(Right<A, B> instance) ;
  }
  
  public interface PartialVisitor<A, B, R> extends Visitor<A, B, R> {
    default R otherwise(Either<A, B> instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Left<A, B> instance) {
      return otherwise((instance));
    }
    
    default R visit(Right<A, B> instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Left<A, B> extends hydra.mantle.Either<A, B> implements Serializable {
    public final A value;
    
    public Left (A value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Left)) {
        return false;
      }
      Left o = (Left) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<A, B, R> visitor) {
      return visitor.visit(this);
    }
  }
  
  public static final class Right<A, B> extends hydra.mantle.Either<A, B> implements Serializable {
    public final B value;
    
    public Right (B value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Right)) {
        return false;
      }
      Right o = (Right) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<A, B, R> visitor) {
      return visitor.visit(this);
    }
  }
}