package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class ExactNumericType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ExactNumericType");
  
  private ExactNumericType () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Numeric instance) ;
    
    R visit(Decimal instance) ;
    
    R visit(Dec instance) ;
    
    R visit(Smallint instance) ;
    
    R visit(Integer_ instance) ;
    
    R visit(Int instance) ;
    
    R visit(Bigint instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ExactNumericType instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Numeric instance) {
      return otherwise((instance));
    }
    
    default R visit(Decimal instance) {
      return otherwise((instance));
    }
    
    default R visit(Dec instance) {
      return otherwise((instance));
    }
    
    default R visit(Smallint instance) {
      return otherwise((instance));
    }
    
    default R visit(Integer_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Int instance) {
      return otherwise((instance));
    }
    
    default R visit(Bigint instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Numeric extends hydra.langs.sql.ansi.ExactNumericType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.ExactNumericType_Numeric_Option> value;
    
    public Numeric (java.util.Optional<hydra.langs.sql.ansi.ExactNumericType_Numeric_Option> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Numeric)) {
        return false;
      }
      Numeric o = (Numeric) (other);
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
  
  public static final class Decimal extends hydra.langs.sql.ansi.ExactNumericType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.ExactNumericType_Decimal_Option> value;
    
    public Decimal (java.util.Optional<hydra.langs.sql.ansi.ExactNumericType_Decimal_Option> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Decimal)) {
        return false;
      }
      Decimal o = (Decimal) (other);
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
  
  public static final class Dec extends hydra.langs.sql.ansi.ExactNumericType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.ExactNumericType_Dec_Option> value;
    
    public Dec (java.util.Optional<hydra.langs.sql.ansi.ExactNumericType_Dec_Option> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Dec)) {
        return false;
      }
      Dec o = (Dec) (other);
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
  
  public static final class Smallint extends hydra.langs.sql.ansi.ExactNumericType implements Serializable {
    public Smallint () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Smallint)) {
        return false;
      }
      Smallint o = (Smallint) (other);
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
  
  public static final class Integer_ extends hydra.langs.sql.ansi.ExactNumericType implements Serializable {
    public Integer_ () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Integer_)) {
        return false;
      }
      Integer_ o = (Integer_) (other);
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
  
  public static final class Int extends hydra.langs.sql.ansi.ExactNumericType implements Serializable {
    public Int () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Int)) {
        return false;
      }
      Int o = (Int) (other);
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
  
  public static final class Bigint extends hydra.langs.sql.ansi.ExactNumericType implements Serializable {
    public Bigint () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Bigint)) {
        return false;
      }
      Bigint o = (Bigint) (other);
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