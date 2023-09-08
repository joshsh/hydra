package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class ValueExpressionPrimary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ValueExpressionPrimary");
  
  private ValueExpressionPrimary () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Parens instance) ;
    
    R visit(Noparens instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ValueExpressionPrimary instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Parens instance) {
      return otherwise((instance));
    }
    
    default R visit(Noparens instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Parens extends hydra.langs.sql.ansi.ValueExpressionPrimary implements Serializable {
    public final hydra.langs.sql.ansi.ParenthesizedValueExpression value;
    
    public Parens (hydra.langs.sql.ansi.ParenthesizedValueExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Parens)) {
        return false;
      }
      Parens o = (Parens) (other);
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
  
  public static final class Noparens extends hydra.langs.sql.ansi.ValueExpressionPrimary implements Serializable {
    public final hydra.langs.sql.ansi.NonparenthesizedValueExpressionPrimary value;
    
    public Noparens (hydra.langs.sql.ansi.NonparenthesizedValueExpressionPrimary value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Noparens)) {
        return false;
      }
      Noparens o = (Noparens) (other);
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