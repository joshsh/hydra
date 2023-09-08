package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class CollectionValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.CollectionValueExpression");
  
  private CollectionValueExpression () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Array instance) ;
    
    R visit(Multiset instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(CollectionValueExpression instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Array instance) {
      return otherwise((instance));
    }
    
    default R visit(Multiset instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Array extends hydra.langs.sql.ansi.CollectionValueExpression implements Serializable {
    public final hydra.langs.sql.ansi.ArrayValueExpression value;
    
    public Array (hydra.langs.sql.ansi.ArrayValueExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Array)) {
        return false;
      }
      Array o = (Array) (other);
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
  
  public static final class Multiset extends hydra.langs.sql.ansi.CollectionValueExpression implements Serializable {
    public final hydra.langs.sql.ansi.MultisetValueExpression value;
    
    public Multiset (hydra.langs.sql.ansi.MultisetValueExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Multiset)) {
        return false;
      }
      Multiset o = (Multiset) (other);
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