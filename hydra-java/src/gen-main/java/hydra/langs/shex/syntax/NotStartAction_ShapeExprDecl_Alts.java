package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class NotStartAction_ShapeExprDecl_Alts implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.NotStartAction.ShapeExprDecl.Alts");
  
  private NotStartAction_ShapeExprDecl_Alts () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(ShapeExpression instance) ;
    
    R visit(EXTERNAL instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(NotStartAction_ShapeExprDecl_Alts instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(ShapeExpression instance) {
      return otherwise((instance));
    }
    
    default R visit(EXTERNAL instance) {
      return otherwise((instance));
    }
  }
  
  public static final class ShapeExpression extends hydra.langs.shex.syntax.NotStartAction_ShapeExprDecl_Alts implements Serializable {
    public final hydra.langs.shex.syntax.ShapeExpression value;
    
    public ShapeExpression (hydra.langs.shex.syntax.ShapeExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ShapeExpression)) {
        return false;
      }
      ShapeExpression o = (ShapeExpression) (other);
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
  
  public static final class EXTERNAL extends hydra.langs.shex.syntax.NotStartAction_ShapeExprDecl_Alts implements Serializable {
    public EXTERNAL () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof EXTERNAL)) {
        return false;
      }
      EXTERNAL o = (EXTERNAL) (other);
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