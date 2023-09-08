package hydra.core;

import java.io.Serializable;

/**
 * A corresponding elimination for an introduction term
 */
public abstract class Elimination<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Elimination");
  
  private Elimination () {
  
  }
  
  public abstract <R> R accept(Visitor<A, R> visitor) ;
  
  public interface Visitor<A, R> {
    R visit(List<A> instance) ;
    
    R visit(Optional<A> instance) ;
    
    R visit(Product<A> instance) ;
    
    R visit(Record<A> instance) ;
    
    R visit(Union<A> instance) ;
    
    R visit(Wrap<A> instance) ;
  }
  
  public interface PartialVisitor<A, R> extends Visitor<A, R> {
    default R otherwise(Elimination<A> instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(List<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Optional<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Product<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Record<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Union<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Wrap<A> instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * Eliminates a list using a fold function; this function has the signature b -&gt; [a] -&gt; b
   */
  public static final class List<A> extends hydra.core.Elimination<A> implements Serializable {
    /**
     * Eliminates a list using a fold function; this function has the signature b -&gt; [a] -&gt; b
     */
    public final hydra.core.Term<A> value;
    
    public List (hydra.core.Term<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof List)) {
        return false;
      }
      List o = (List) (other);
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
   * Eliminates an optional term by matching over the two possible cases
   */
  public static final class Optional<A> extends hydra.core.Elimination<A> implements Serializable {
    /**
     * Eliminates an optional term by matching over the two possible cases
     */
    public final hydra.core.OptionalCases<A> value;
    
    public Optional (hydra.core.OptionalCases<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Optional)) {
        return false;
      }
      Optional o = (Optional) (other);
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
   * Eliminates a tuple by projecting the component at a given 0-indexed offset
   */
  public static final class Product<A> extends hydra.core.Elimination<A> implements Serializable {
    /**
     * Eliminates a tuple by projecting the component at a given 0-indexed offset
     */
    public final hydra.core.TupleProjection value;
    
    public Product (hydra.core.TupleProjection value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Product)) {
        return false;
      }
      Product o = (Product) (other);
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
   * Eliminates a record by projecting a given field
   */
  public static final class Record<A> extends hydra.core.Elimination<A> implements Serializable {
    /**
     * Eliminates a record by projecting a given field
     */
    public final hydra.core.Projection value;
    
    public Record (hydra.core.Projection value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Record)) {
        return false;
      }
      Record o = (Record) (other);
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
   * Eliminates a union term by matching over the fields of the union. This is a case statement.
   */
  public static final class Union<A> extends hydra.core.Elimination<A> implements Serializable {
    /**
     * Eliminates a union term by matching over the fields of the union. This is a case statement.
     */
    public final hydra.core.CaseStatement<A> value;
    
    public Union (hydra.core.CaseStatement<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Union)) {
        return false;
      }
      Union o = (Union) (other);
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
   * Unwrap a wrapped term
   */
  public static final class Wrap<A> extends hydra.core.Elimination<A> implements Serializable {
    /**
     * Unwrap a wrapped term
     */
    public final hydra.core.Name value;
    
    public Wrap (hydra.core.Name value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Wrap)) {
        return false;
      }
      Wrap o = (Wrap) (other);
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