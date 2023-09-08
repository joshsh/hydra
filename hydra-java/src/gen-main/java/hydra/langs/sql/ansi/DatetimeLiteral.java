package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class DatetimeLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.DatetimeLiteral");
  
  private DatetimeLiteral () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Date instance) ;
    
    R visit(Time instance) ;
    
    R visit(Timestamp instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(DatetimeLiteral instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Date instance) {
      return otherwise((instance));
    }
    
    default R visit(Time instance) {
      return otherwise((instance));
    }
    
    default R visit(Timestamp instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Date extends hydra.langs.sql.ansi.DatetimeLiteral implements Serializable {
    public final hydra.langs.sql.ansi.DateLiteral value;
    
    public Date (hydra.langs.sql.ansi.DateLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Date)) {
        return false;
      }
      Date o = (Date) (other);
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
  
  public static final class Time extends hydra.langs.sql.ansi.DatetimeLiteral implements Serializable {
    public final hydra.langs.sql.ansi.TimeLiteral value;
    
    public Time (hydra.langs.sql.ansi.TimeLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Time)) {
        return false;
      }
      Time o = (Time) (other);
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
  
  public static final class Timestamp extends hydra.langs.sql.ansi.DatetimeLiteral implements Serializable {
    public final hydra.langs.sql.ansi.TimestampLiteral value;
    
    public Timestamp (hydra.langs.sql.ansi.TimestampLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Timestamp)) {
        return false;
      }
      Timestamp o = (Timestamp) (other);
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