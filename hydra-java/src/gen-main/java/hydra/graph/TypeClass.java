package hydra.graph;

import java.io.Serializable;

/**
 * Any of a small number of built-in type classes
 */
public abstract class TypeClass implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/graph.TypeClass");
  
  private TypeClass () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Equality instance) ;
    
    R visit(Ordering instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TypeClass instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Equality instance) {
      return otherwise((instance));
    }
    
    default R visit(Ordering instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Equality extends hydra.graph.TypeClass implements Serializable {
    public Equality () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Equality)) {
        return false;
      }
      Equality o = (Equality) (other);
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
  
  public static final class Ordering extends hydra.graph.TypeClass implements Serializable {
    public Ordering () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Ordering)) {
        return false;
      }
      Ordering o = (Ordering) (other);
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