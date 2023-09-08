package hydra.core;

import java.io.Serializable;

/**
 * A data type
 */
public abstract class Type<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Type");
  
  private Type () {
  
  }
  
  public abstract <R> R accept(Visitor<A, R> visitor) ;
  
  public interface Visitor<A, R> {
    R visit(Annotated<A> instance) ;
    
    R visit(Application<A> instance) ;
    
    R visit(Function<A> instance) ;
    
    R visit(Lambda<A> instance) ;
    
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
    default R otherwise(Type<A> instance) {
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
    
    default R visit(Lambda<A> instance) {
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
   * A type annotated with metadata
   */
  public static final class Annotated<A> extends hydra.core.Type<A> implements Serializable {
    /**
     * A type annotated with metadata
     */
    public final hydra.core.Annotated<hydra.core.Type<A>, A> value;
    
    public Annotated (hydra.core.Annotated<hydra.core.Type<A>, A> value) {
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
  
  public static final class Application<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.ApplicationType<A> value;
    
    public Application (hydra.core.ApplicationType<A> value) {
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
  
  public static final class Function<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.FunctionType<A> value;
    
    public Function (hydra.core.FunctionType<A> value) {
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
  
  public static final class Lambda<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.LambdaType<A> value;
    
    public Lambda (hydra.core.LambdaType<A> value) {
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
  
  public static final class List<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.Type<A> value;
    
    public List (hydra.core.Type<A> value) {
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
  
  public static final class Literal<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.LiteralType value;
    
    public Literal (hydra.core.LiteralType value) {
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
  
  public static final class Map<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.MapType<A> value;
    
    public Map (hydra.core.MapType<A> value) {
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
  
  public static final class Optional<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.Type<A> value;
    
    public Optional (hydra.core.Type<A> value) {
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
  
  public static final class Product<A> extends hydra.core.Type<A> implements Serializable {
    public final java.util.List<hydra.core.Type<A>> value;
    
    public Product (java.util.List<hydra.core.Type<A>> value) {
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
  
  public static final class Record<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.RowType<A> value;
    
    public Record (hydra.core.RowType<A> value) {
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
  
  public static final class Set<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.Type<A> value;
    
    public Set (hydra.core.Type<A> value) {
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
  
  public static final class Stream<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.Type<A> value;
    
    public Stream (hydra.core.Type<A> value) {
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
  
  public static final class Sum<A> extends hydra.core.Type<A> implements Serializable {
    public final java.util.List<hydra.core.Type<A>> value;
    
    public Sum (java.util.List<hydra.core.Type<A>> value) {
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
  
  public static final class Union<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.RowType<A> value;
    
    public Union (hydra.core.RowType<A> value) {
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
  
  public static final class Variable<A> extends hydra.core.Type<A> implements Serializable {
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
  
  public static final class Wrap<A> extends hydra.core.Type<A> implements Serializable {
    public final hydra.core.Nominal<hydra.core.Type<A>> value;
    
    public Wrap (hydra.core.Nominal<hydra.core.Type<A>> value) {
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