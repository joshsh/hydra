package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class BooleanPrimary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BooleanPrimary");
  
  private BooleanPrimary () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Predicate instance) ;
    
    R visit(Predicand instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(BooleanPrimary instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Predicate instance) {
      return otherwise((instance));
    }
    
    default R visit(Predicand instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Predicate extends hydra.langs.sql.ansi.BooleanPrimary implements Serializable {
    public final hydra.langs.sql.ansi.Predicate value;
    
    public Predicate (hydra.langs.sql.ansi.Predicate value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Predicate)) {
        return false;
      }
      Predicate o = (Predicate) (other);
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
  
  public static final class Predicand extends hydra.langs.sql.ansi.BooleanPrimary implements Serializable {
    public final hydra.langs.sql.ansi.BooleanPredicand value;
    
    public Predicand (hydra.langs.sql.ansi.BooleanPredicand value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Predicand)) {
        return false;
      }
      Predicand o = (Predicand) (other);
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