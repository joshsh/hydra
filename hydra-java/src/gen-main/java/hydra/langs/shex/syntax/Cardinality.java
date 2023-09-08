package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class Cardinality implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Cardinality");
  
  private Cardinality () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Ast instance) ;
    
    R visit(Plus instance) ;
    
    R visit(Quest instance) ;
    
    R visit(RepeatRange instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Cardinality instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Ast instance) {
      return otherwise((instance));
    }
    
    default R visit(Plus instance) {
      return otherwise((instance));
    }
    
    default R visit(Quest instance) {
      return otherwise((instance));
    }
    
    default R visit(RepeatRange instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Ast extends hydra.langs.shex.syntax.Cardinality implements Serializable {
    public Ast () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Ast)) {
        return false;
      }
      Ast o = (Ast) (other);
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
  
  public static final class Plus extends hydra.langs.shex.syntax.Cardinality implements Serializable {
    public Plus () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Plus)) {
        return false;
      }
      Plus o = (Plus) (other);
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
  
  public static final class Quest extends hydra.langs.shex.syntax.Cardinality implements Serializable {
    public Quest () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Quest)) {
        return false;
      }
      Quest o = (Quest) (other);
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
  
  public static final class RepeatRange extends hydra.langs.shex.syntax.Cardinality implements Serializable {
    public final hydra.langs.shex.syntax.RepeatRange value;
    
    public RepeatRange (hydra.langs.shex.syntax.RepeatRange value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof RepeatRange)) {
        return false;
      }
      RepeatRange o = (RepeatRange) (other);
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