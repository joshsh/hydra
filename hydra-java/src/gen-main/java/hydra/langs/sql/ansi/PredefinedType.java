package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class PredefinedType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.PredefinedType");
  
  private PredefinedType () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(String_ instance) ;
    
    R visit(NationalString instance) ;
    
    R visit(Blob instance) ;
    
    R visit(Numeric instance) ;
    
    R visit(Boolean_ instance) ;
    
    R visit(Datetime instance) ;
    
    R visit(Interval instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(PredefinedType instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(String_ instance) {
      return otherwise((instance));
    }
    
    default R visit(NationalString instance) {
      return otherwise((instance));
    }
    
    default R visit(Blob instance) {
      return otherwise((instance));
    }
    
    default R visit(Numeric instance) {
      return otherwise((instance));
    }
    
    default R visit(Boolean_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Datetime instance) {
      return otherwise((instance));
    }
    
    default R visit(Interval instance) {
      return otherwise((instance));
    }
  }
  
  public static final class String_ extends hydra.langs.sql.ansi.PredefinedType implements Serializable {
    public final hydra.langs.sql.ansi.PredefinedType_String value;
    
    public String_ (hydra.langs.sql.ansi.PredefinedType_String value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof String_)) {
        return false;
      }
      String_ o = (String_) (other);
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
  
  public static final class NationalString extends hydra.langs.sql.ansi.PredefinedType implements Serializable {
    public final hydra.langs.sql.ansi.PredefinedType_NationalString value;
    
    public NationalString (hydra.langs.sql.ansi.PredefinedType_NationalString value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NationalString)) {
        return false;
      }
      NationalString o = (NationalString) (other);
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
  
  public static final class Blob extends hydra.langs.sql.ansi.PredefinedType implements Serializable {
    public final hydra.langs.sql.ansi.BinaryLargeObjectStringType value;
    
    public Blob (hydra.langs.sql.ansi.BinaryLargeObjectStringType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Blob)) {
        return false;
      }
      Blob o = (Blob) (other);
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
  
  public static final class Numeric extends hydra.langs.sql.ansi.PredefinedType implements Serializable {
    public final hydra.langs.sql.ansi.NumericType value;
    
    public Numeric (hydra.langs.sql.ansi.NumericType value) {
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
  
  public static final class Boolean_ extends hydra.langs.sql.ansi.PredefinedType implements Serializable {
    public final hydra.langs.sql.ansi.BooleanType value;
    
    public Boolean_ (hydra.langs.sql.ansi.BooleanType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Boolean_)) {
        return false;
      }
      Boolean_ o = (Boolean_) (other);
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
  
  public static final class Datetime extends hydra.langs.sql.ansi.PredefinedType implements Serializable {
    public final hydra.langs.sql.ansi.DatetimeType value;
    
    public Datetime (hydra.langs.sql.ansi.DatetimeType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Datetime)) {
        return false;
      }
      Datetime o = (Datetime) (other);
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
  
  public static final class Interval extends hydra.langs.sql.ansi.PredefinedType implements Serializable {
    public final hydra.langs.sql.ansi.IntervalType value;
    
    public Interval (hydra.langs.sql.ansi.IntervalType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Interval)) {
        return false;
      }
      Interval o = (Interval) (other);
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