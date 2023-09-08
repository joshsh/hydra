package hydra.ast;

import java.io.Serializable;

/**
 * One of several classes of whitespace
 */
public abstract class Ws implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ast.Ws");
  
  private Ws () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(None instance) ;
    
    R visit(Space instance) ;
    
    R visit(Break instance) ;
    
    R visit(BreakAndIndent instance) ;
    
    R visit(DoubleBreak instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Ws instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(None instance) {
      return otherwise((instance));
    }
    
    default R visit(Space instance) {
      return otherwise((instance));
    }
    
    default R visit(Break instance) {
      return otherwise((instance));
    }
    
    default R visit(BreakAndIndent instance) {
      return otherwise((instance));
    }
    
    default R visit(DoubleBreak instance) {
      return otherwise((instance));
    }
  }
  
  public static final class None extends hydra.ast.Ws implements Serializable {
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
  
  public static final class Space extends hydra.ast.Ws implements Serializable {
    public Space () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Space)) {
        return false;
      }
      Space o = (Space) (other);
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
  
  public static final class Break extends hydra.ast.Ws implements Serializable {
    public Break () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Break)) {
        return false;
      }
      Break o = (Break) (other);
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
  
  public static final class BreakAndIndent extends hydra.ast.Ws implements Serializable {
    public final String value;
    
    public BreakAndIndent (String value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof BreakAndIndent)) {
        return false;
      }
      BreakAndIndent o = (BreakAndIndent) (other);
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
  
  public static final class DoubleBreak extends hydra.ast.Ws implements Serializable {
    public DoubleBreak () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DoubleBreak)) {
        return false;
      }
      DoubleBreak o = (DoubleBreak) (other);
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