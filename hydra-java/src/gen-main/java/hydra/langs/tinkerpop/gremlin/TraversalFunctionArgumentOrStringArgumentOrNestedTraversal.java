// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.gremlin;

import java.io.Serializable;

public abstract class TraversalFunctionArgumentOrStringArgumentOrNestedTraversal implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/gremlin.TraversalFunctionArgumentOrStringArgumentOrNestedTraversal");
  
  private TraversalFunctionArgumentOrStringArgumentOrNestedTraversal () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Function instance) ;
    
    R visit(String_ instance) ;
    
    R visit(Traversal instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TraversalFunctionArgumentOrStringArgumentOrNestedTraversal instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Function instance) {
      return otherwise((instance));
    }
    
    default R visit(String_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Traversal instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Function extends hydra.langs.tinkerpop.gremlin.TraversalFunctionArgumentOrStringArgumentOrNestedTraversal implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.TraversalFunctionArgument value;
    
    public Function (hydra.langs.tinkerpop.gremlin.TraversalFunctionArgument value) {
      java.util.Objects.requireNonNull((value));
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
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
  
  public static final class String_ extends hydra.langs.tinkerpop.gremlin.TraversalFunctionArgumentOrStringArgumentOrNestedTraversal implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public String_ (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      java.util.Objects.requireNonNull((value));
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
  
  public static final class Traversal extends hydra.langs.tinkerpop.gremlin.TraversalFunctionArgumentOrStringArgumentOrNestedTraversal implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.NestedTraversal value;
    
    public Traversal (hydra.langs.tinkerpop.gremlin.NestedTraversal value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Traversal)) {
        return false;
      }
      Traversal o = (Traversal) (other);
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