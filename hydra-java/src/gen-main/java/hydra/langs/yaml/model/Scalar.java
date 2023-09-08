package hydra.langs.yaml.model;

import java.io.Serializable;

/**
 * A union of scalars supported in the YAML failsafe and JSON schemas. Other scalars are not supported here
 */
public abstract class Scalar implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/yaml/model.Scalar");
  
  private Scalar () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Bool instance) ;
    
    R visit(Float_ instance) ;
    
    R visit(Int instance) ;
    
    R visit(Null instance) ;
    
    R visit(Str instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Scalar instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Bool instance) {
      return otherwise((instance));
    }
    
    default R visit(Float_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Int instance) {
      return otherwise((instance));
    }
    
    default R visit(Null instance) {
      return otherwise((instance));
    }
    
    default R visit(Str instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * Represents a true/false value
   */
  public static final class Bool extends hydra.langs.yaml.model.Scalar implements Serializable {
    /**
     * Represents a true/false value
     */
    public final Boolean value;
    
    public Bool (Boolean value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Bool)) {
        return false;
      }
      Bool o = (Bool) (other);
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
  
  public static final class Float_ extends hydra.langs.yaml.model.Scalar implements Serializable {
    public final Double value;
    
    public Float_ (Double value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Float_)) {
        return false;
      }
      Float_ o = (Float_) (other);
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
  
  /**
   * Represents arbitrary sized finite mathematical integers
   */
  public static final class Int extends hydra.langs.yaml.model.Scalar implements Serializable {
    /**
     * Represents arbitrary sized finite mathematical integers
     */
    public final java.math.BigInteger value;
    
    public Int (java.math.BigInteger value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Int)) {
        return false;
      }
      Int o = (Int) (other);
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
  
  /**
   * Represents the lack of a value
   */
  public static final class Null extends hydra.langs.yaml.model.Scalar implements Serializable {
    public Null () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Null)) {
        return false;
      }
      Null o = (Null) (other);
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
  
  /**
   * A string value
   */
  public static final class Str extends hydra.langs.yaml.model.Scalar implements Serializable {
    /**
     * A string value
     */
    public final String value;
    
    public Str (String value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Str)) {
        return false;
      }
      Str o = (Str) (other);
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