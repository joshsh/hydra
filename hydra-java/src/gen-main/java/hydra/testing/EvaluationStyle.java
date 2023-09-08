package hydra.testing;

import java.io.Serializable;

/**
 * One of two evaluation styles: eager or lazy
 */
public abstract class EvaluationStyle implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/testing.EvaluationStyle");
  
  private EvaluationStyle () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Eager instance) ;
    
    R visit(Lazy instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(EvaluationStyle instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Eager instance) {
      return otherwise((instance));
    }
    
    default R visit(Lazy instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Eager extends hydra.testing.EvaluationStyle implements Serializable {
    public Eager () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Eager)) {
        return false;
      }
      Eager o = (Eager) (other);
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
  
  public static final class Lazy extends hydra.testing.EvaluationStyle implements Serializable {
    public Lazy () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Lazy)) {
        return false;
      }
      Lazy o = (Lazy) (other);
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