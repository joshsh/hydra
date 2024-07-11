// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.gremlin;

import java.io.Serializable;

public abstract class TraversalFunction implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/gremlin.TraversalFunction");
  
  private TraversalFunction () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Token instance) ;
    
    R visit(Column instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TraversalFunction instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Token instance) {
      return otherwise((instance));
    }
    
    default R visit(Column instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Token extends hydra.langs.tinkerpop.gremlin.TraversalFunction implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.TraversalToken value;
    
    public Token (hydra.langs.tinkerpop.gremlin.TraversalToken value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Token)) {
        return false;
      }
      Token o = (Token) (other);
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
  
  public static final class Column extends hydra.langs.tinkerpop.gremlin.TraversalFunction implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.TraversalColumn value;
    
    public Column (hydra.langs.tinkerpop.gremlin.TraversalColumn value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Column)) {
        return false;
      }
      Column o = (Column) (other);
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