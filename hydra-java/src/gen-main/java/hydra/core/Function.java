package hydra.core;

import java.io.Serializable;

/**
 * A function
 */
public abstract class Function<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Function");
  
  private Function () {
  
  }
  
  public abstract <R> R accept(Visitor<A, R> visitor) ;
  
  public interface Visitor<A, R> {
    R visit(Elimination<A> instance) ;
    
    R visit(Lambda<A> instance) ;
    
    R visit(Primitive<A> instance) ;
  }
  
  public interface PartialVisitor<A, R> extends Visitor<A, R> {
    default R otherwise(Function<A> instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Elimination<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Lambda<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Primitive<A> instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * An elimination for any of a few term variants
   */
  public static final class Elimination<A> extends hydra.core.Function<A> implements Serializable {
    /**
     * An elimination for any of a few term variants
     */
    public final hydra.core.Elimination<A> value;
    
    public Elimination (hydra.core.Elimination<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Elimination)) {
        return false;
      }
      Elimination o = (Elimination) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<A, R> visitor) {
      return visitor.visit(this);
    }
  }
  
  /**
   * A function abstraction (lambda)
   */
  public static final class Lambda<A> extends hydra.core.Function<A> implements Serializable {
    /**
     * A function abstraction (lambda)
     */
    public final hydra.core.Lambda<A> value;
    
    public Lambda (hydra.core.Lambda<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Lambda)) {
        return false;
      }
      Lambda o = (Lambda) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<A, R> visitor) {
      return visitor.visit(this);
    }
  }
  
  /**
   * A reference to a built-in (primitive) function
   */
  public static final class Primitive<A> extends hydra.core.Function<A> implements Serializable {
    /**
     * A reference to a built-in (primitive) function
     */
    public final hydra.core.Name value;
    
    public Primitive (hydra.core.Name value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Primitive)) {
        return false;
      }
      Primitive o = (Primitive) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<A, R> visitor) {
      return visitor.visit(this);
    }
  }
}