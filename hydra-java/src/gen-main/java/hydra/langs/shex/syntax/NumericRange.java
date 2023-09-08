package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class NumericRange implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.NumericRange");
  
  private NumericRange () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(MININCLUSIVE instance) ;
    
    R visit(MINEXCLUSIVE instance) ;
    
    R visit(MAXINCLUSIVE instance) ;
    
    R visit(MAXEXCLUSIVE instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(NumericRange instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(MININCLUSIVE instance) {
      return otherwise((instance));
    }
    
    default R visit(MINEXCLUSIVE instance) {
      return otherwise((instance));
    }
    
    default R visit(MAXINCLUSIVE instance) {
      return otherwise((instance));
    }
    
    default R visit(MAXEXCLUSIVE instance) {
      return otherwise((instance));
    }
  }
  
  public static final class MININCLUSIVE extends hydra.langs.shex.syntax.NumericRange implements Serializable {
    public MININCLUSIVE () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MININCLUSIVE)) {
        return false;
      }
      MININCLUSIVE o = (MININCLUSIVE) (other);
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
  
  public static final class MINEXCLUSIVE extends hydra.langs.shex.syntax.NumericRange implements Serializable {
    public MINEXCLUSIVE () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MINEXCLUSIVE)) {
        return false;
      }
      MINEXCLUSIVE o = (MINEXCLUSIVE) (other);
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
  
  public static final class MAXINCLUSIVE extends hydra.langs.shex.syntax.NumericRange implements Serializable {
    public MAXINCLUSIVE () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MAXINCLUSIVE)) {
        return false;
      }
      MAXINCLUSIVE o = (MAXINCLUSIVE) (other);
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
  
  public static final class MAXEXCLUSIVE extends hydra.langs.shex.syntax.NumericRange implements Serializable {
    public MAXEXCLUSIVE () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MAXEXCLUSIVE)) {
        return false;
      }
      MAXEXCLUSIVE o = (MAXEXCLUSIVE) (other);
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