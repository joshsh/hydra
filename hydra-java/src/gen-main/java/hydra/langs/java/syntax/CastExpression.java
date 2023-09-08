package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class CastExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.CastExpression");
  
  private CastExpression () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Primitive instance) ;
    
    R visit(NotPlusMinus instance) ;
    
    R visit(Lambda instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(CastExpression instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Primitive instance) {
      return otherwise((instance));
    }
    
    default R visit(NotPlusMinus instance) {
      return otherwise((instance));
    }
    
    default R visit(Lambda instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Primitive extends hydra.langs.java.syntax.CastExpression implements Serializable {
    public final hydra.langs.java.syntax.CastExpression_Primitive value;
    
    public Primitive (hydra.langs.java.syntax.CastExpression_Primitive value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Primitive)) {
        return false;
      }
      Primitive o = (Primitive) (other);
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
  
  public static final class NotPlusMinus extends hydra.langs.java.syntax.CastExpression implements Serializable {
    public final hydra.langs.java.syntax.CastExpression_NotPlusMinus value;
    
    public NotPlusMinus (hydra.langs.java.syntax.CastExpression_NotPlusMinus value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NotPlusMinus)) {
        return false;
      }
      NotPlusMinus o = (NotPlusMinus) (other);
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
  
  public static final class Lambda extends hydra.langs.java.syntax.CastExpression implements Serializable {
    public final hydra.langs.java.syntax.CastExpression_Lambda value;
    
    public Lambda (hydra.langs.java.syntax.CastExpression_Lambda value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Lambda)) {
        return false;
      }
      Lambda o = (Lambda) (other);
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