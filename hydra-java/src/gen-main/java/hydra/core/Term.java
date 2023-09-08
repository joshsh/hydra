package hydra.core;

import java.io.Serializable;

/**
 * A data term
 */
public abstract class Term<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Term");
  
  private Term () {
  
  }
  
  public abstract <R> R accept(Visitor<A, R> visitor) ;
  
  public interface Visitor<A, R> {
    R visit(Annotated<A> instance) ;
    
    R visit(Application<A> instance) ;
    
    R visit(Function<A> instance) ;
    
    R visit(Let<A> instance) ;
    
    R visit(List<A> instance) ;
    
    R visit(Literal<A> instance) ;
    
    R visit(Map<A> instance) ;
    
    R visit(Optional<A> instance) ;
    
    R visit(Product<A> instance) ;
    
    R visit(Record<A> instance) ;
    
    R visit(Set<A> instance) ;
    
    R visit(Stream<A> instance) ;
    
    R visit(Sum<A> instance) ;
    
    R visit(Union<A> instance) ;
    
    R visit(Variable<A> instance) ;
    
    R visit(Wrap<A> instance) ;
  }
  
  public interface PartialVisitor<A, R> extends Visitor<A, R> {
    default R otherwise(Term<A> instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Annotated<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Application<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Function<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Let<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(List<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Literal<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Map<A> instance) {
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
    
    default R visit(Set<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Stream<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Sum<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Union<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Variable<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Wrap<A> instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * A term annotated with metadata
   */
  public static final class Annotated<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A term annotated with metadata
     */
    public final hydra.core.Annotated<hydra.core.Term<A>, A> value;
    
    public Annotated (hydra.core.Annotated<hydra.core.Term<A>, A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Annotated)) {
        return false;
      }
      Annotated o = (Annotated) (other);
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
   * A function application
   */
  public static final class Application<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A function application
     */
    public final hydra.core.Application<A> value;
    
    public Application (hydra.core.Application<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Application)) {
        return false;
      }
      Application o = (Application) (other);
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
   * A function term
   */
  public static final class Function<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A function term
     */
    public final hydra.core.Function<A> value;
    
    public Function (hydra.core.Function<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Function)) {
        return false;
      }
      Function o = (Function) (other);
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
  
  public static final class Let<A> extends hydra.core.Term<A> implements Serializable {
    public final hydra.core.Let<A> value;
    
    public Let (hydra.core.Let<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Let)) {
        return false;
      }
      Let o = (Let) (other);
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
   * A list
   */
  public static final class List<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A list
     */
    public final java.util.List<hydra.core.Term<A>> value;
    
    public List (java.util.List<hydra.core.Term<A>> value) {
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
   * A literal value
   */
  public static final class Literal<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A literal value
     */
    public final hydra.core.Literal value;
    
    public Literal (hydra.core.Literal value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Literal)) {
        return false;
      }
      Literal o = (Literal) (other);
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
   * A map of keys to values
   */
  public static final class Map<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A map of keys to values
     */
    public final java.util.Map<hydra.core.Term<A>, hydra.core.Term<A>> value;
    
    public Map (java.util.Map<hydra.core.Term<A>, hydra.core.Term<A>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Map)) {
        return false;
      }
      Map o = (Map) (other);
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
   * An optional value
   */
  public static final class Optional<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * An optional value
     */
    public final java.util.Optional<hydra.core.Term<A>> value;
    
    public Optional (java.util.Optional<hydra.core.Term<A>> value) {
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
   * A tuple
   */
  public static final class Product<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A tuple
     */
    public final java.util.List<hydra.core.Term<A>> value;
    
    public Product (java.util.List<hydra.core.Term<A>> value) {
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
   * A record term
   */
  public static final class Record<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A record term
     */
    public final hydra.core.Record<A> value;
    
    public Record (hydra.core.Record<A> value) {
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
   * A set of values
   */
  public static final class Set<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A set of values
     */
    public final java.util.Set<hydra.core.Term<A>> value;
    
    public Set (java.util.Set<hydra.core.Term<A>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Set)) {
        return false;
      }
      Set o = (Set) (other);
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
   * An infinite stream of terms
   */
  public static final class Stream<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * An infinite stream of terms
     */
    public final hydra.core.Stream<A> value;
    
    public Stream (hydra.core.Stream<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Stream)) {
        return false;
      }
      Stream o = (Stream) (other);
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
   * A variant tuple
   */
  public static final class Sum<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A variant tuple
     */
    public final hydra.core.Sum<A> value;
    
    public Sum (hydra.core.Sum<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sum)) {
        return false;
      }
      Sum o = (Sum) (other);
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
   * An injection; an instance of a union type
   */
  public static final class Union<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * An injection; an instance of a union type
     */
    public final hydra.core.Injection<A> value;
    
    public Union (hydra.core.Injection<A> value) {
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
   * A variable reference
   */
  public static final class Variable<A> extends hydra.core.Term<A> implements Serializable {
    /**
     * A variable reference
     */
    public final hydra.core.Name value;
    
    public Variable (hydra.core.Name value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Variable)) {
        return false;
      }
      Variable o = (Variable) (other);
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
  
  public static final class Wrap<A> extends hydra.core.Term<A> implements Serializable {
    public final hydra.core.Nominal<hydra.core.Term<A>> value;
    
    public Wrap (hydra.core.Nominal<hydra.core.Term<A>> value) {
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