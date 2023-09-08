package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class GeneralLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.GeneralLiteral");
  
  private GeneralLiteral () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(String_ instance) ;
    
    R visit(NationalString instance) ;
    
    R visit(Unicode instance) ;
    
    R visit(Binary instance) ;
    
    R visit(DateTime instance) ;
    
    R visit(Interval instance) ;
    
    R visit(Boolean_ instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(GeneralLiteral instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(String_ instance) {
      return otherwise((instance));
    }
    
    default R visit(NationalString instance) {
      return otherwise((instance));
    }
    
    default R visit(Unicode instance) {
      return otherwise((instance));
    }
    
    default R visit(Binary instance) {
      return otherwise((instance));
    }
    
    default R visit(DateTime instance) {
      return otherwise((instance));
    }
    
    default R visit(Interval instance) {
      return otherwise((instance));
    }
    
    default R visit(Boolean_ instance) {
      return otherwise((instance));
    }
  }
  
  public static final class String_ extends hydra.langs.sql.ansi.GeneralLiteral implements Serializable {
    public final hydra.langs.sql.ansi.CharacterStringLiteral value;
    
    public String_ (hydra.langs.sql.ansi.CharacterStringLiteral value) {
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
  
  public static final class NationalString extends hydra.langs.sql.ansi.GeneralLiteral implements Serializable {
    public final hydra.langs.sql.ansi.NationalCharacterStringLiteral value;
    
    public NationalString (hydra.langs.sql.ansi.NationalCharacterStringLiteral value) {
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
  
  public static final class Unicode extends hydra.langs.sql.ansi.GeneralLiteral implements Serializable {
    public final hydra.langs.sql.ansi.UnicodeCharacterStringLiteral value;
    
    public Unicode (hydra.langs.sql.ansi.UnicodeCharacterStringLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Unicode)) {
        return false;
      }
      Unicode o = (Unicode) (other);
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
  
  public static final class Binary extends hydra.langs.sql.ansi.GeneralLiteral implements Serializable {
    public final hydra.langs.sql.ansi.BinaryStringLiteral value;
    
    public Binary (hydra.langs.sql.ansi.BinaryStringLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Binary)) {
        return false;
      }
      Binary o = (Binary) (other);
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
  
  public static final class DateTime extends hydra.langs.sql.ansi.GeneralLiteral implements Serializable {
    public final hydra.langs.sql.ansi.DatetimeLiteral value;
    
    public DateTime (hydra.langs.sql.ansi.DatetimeLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DateTime)) {
        return false;
      }
      DateTime o = (DateTime) (other);
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
  
  public static final class Interval extends hydra.langs.sql.ansi.GeneralLiteral implements Serializable {
    public final hydra.langs.sql.ansi.IntervalLiteral value;
    
    public Interval (hydra.langs.sql.ansi.IntervalLiteral value) {
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
  
  public static final class Boolean_ extends hydra.langs.sql.ansi.GeneralLiteral implements Serializable {
    public final hydra.langs.sql.ansi.BooleanLiteral value;
    
    public Boolean_ (hydra.langs.sql.ansi.BooleanLiteral value) {
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
}