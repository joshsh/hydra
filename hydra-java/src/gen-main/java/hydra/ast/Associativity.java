package hydra.ast;

import java.io.Serializable;

/**
 * Operator associativity
 */
public abstract class Associativity implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ast.Associativity");
  
  private Associativity () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(None instance) ;
    
    R visit(Left instance) ;
    
    R visit(Right instance) ;
    
    R visit(Both instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Associativity instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(None instance) {
      return otherwise((instance));
    }
    
    default R visit(Left instance) {
      return otherwise((instance));
    }
    
    default R visit(Right instance) {
      return otherwise((instance));
    }
    
    default R visit(Both instance) {
      return otherwise((instance));
    }
  }
  
  public static final class None extends hydra.ast.Associativity implements Serializable {
    public None () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof None)) {
        return false;
      }
      None o = (None) (other);
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
  
  public static final class Left extends hydra.ast.Associativity implements Serializable {
    public Left () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Left)) {
        return false;
      }
      Left o = (Left) (other);
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
  
  public static final class Right extends hydra.ast.Associativity implements Serializable {
    public Right () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Right)) {
        return false;
      }
      Right o = (Right) (other);
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
  
  public static final class Both extends hydra.ast.Associativity implements Serializable {
    public Both () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Both)) {
        return false;
      }
      Both o = (Both) (other);
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