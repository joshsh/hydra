package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class UnsignedNumericLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.UnsignedNumericLiteral");
  
  private UnsignedNumericLiteral () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Exact instance) ;
    
    R visit(Approximate instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(UnsignedNumericLiteral instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Exact instance) {
      return otherwise((instance));
    }
    
    default R visit(Approximate instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Exact extends hydra.langs.sql.ansi.UnsignedNumericLiteral implements Serializable {
    public final hydra.langs.sql.ansi.ExactNumericLiteral value;
    
    public Exact (hydra.langs.sql.ansi.ExactNumericLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Exact)) {
        return false;
      }
      Exact o = (Exact) (other);
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
  
  public static final class Approximate extends hydra.langs.sql.ansi.UnsignedNumericLiteral implements Serializable {
    public final hydra.langs.sql.ansi.ApproximateNumericLiteral value;
    
    public Approximate (hydra.langs.sql.ansi.ApproximateNumericLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Approximate)) {
        return false;
      }
      Approximate o = (Approximate) (other);
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