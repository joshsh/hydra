package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class UnaryExpressionNotPlusMinus implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.UnaryExpressionNotPlusMinus");
  
  private UnaryExpressionNotPlusMinus () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Postfix instance) ;
    
    R visit(Tilde instance) ;
    
    R visit(Not instance) ;
    
    R visit(Cast instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(UnaryExpressionNotPlusMinus instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Postfix instance) {
      return otherwise((instance));
    }
    
    default R visit(Tilde instance) {
      return otherwise((instance));
    }
    
    default R visit(Not instance) {
      return otherwise((instance));
    }
    
    default R visit(Cast instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Postfix extends hydra.langs.java.syntax.UnaryExpressionNotPlusMinus implements Serializable {
    public final hydra.langs.java.syntax.PostfixExpression value;
    
    public Postfix (hydra.langs.java.syntax.PostfixExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Postfix)) {
        return false;
      }
      Postfix o = (Postfix) (other);
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
  
  public static final class Tilde extends hydra.langs.java.syntax.UnaryExpressionNotPlusMinus implements Serializable {
    public final hydra.langs.java.syntax.UnaryExpression value;
    
    public Tilde (hydra.langs.java.syntax.UnaryExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Tilde)) {
        return false;
      }
      Tilde o = (Tilde) (other);
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
  
  public static final class Not extends hydra.langs.java.syntax.UnaryExpressionNotPlusMinus implements Serializable {
    public final hydra.langs.java.syntax.UnaryExpression value;
    
    public Not (hydra.langs.java.syntax.UnaryExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Not)) {
        return false;
      }
      Not o = (Not) (other);
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
  
  public static final class Cast extends hydra.langs.java.syntax.UnaryExpressionNotPlusMinus implements Serializable {
    public final hydra.langs.java.syntax.CastExpression value;
    
    public Cast (hydra.langs.java.syntax.CastExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Cast)) {
        return false;
      }
      Cast o = (Cast) (other);
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