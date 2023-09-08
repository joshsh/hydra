package hydra.ast;

import java.io.Serializable;

/**
 * An expression indented in a certain style
 */
public class IndentedExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ast.IndentedExpression");
  
  public final hydra.ast.IndentStyle style;
  
  public final hydra.ast.Expr expr;
  
  public IndentedExpression (hydra.ast.IndentStyle style, hydra.ast.Expr expr) {
    this.style = style;
    this.expr = expr;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IndentedExpression)) {
      return false;
    }
    IndentedExpression o = (IndentedExpression) (other);
    return style.equals(o.style) && expr.equals(o.expr);
  }
  
  @Override
  public int hashCode() {
    return 2 * style.hashCode() + 3 * expr.hashCode();
  }
  
  public IndentedExpression withStyle(hydra.ast.IndentStyle style) {
    return new IndentedExpression(style, expr);
  }
  
  public IndentedExpression withExpr(hydra.ast.Expr expr) {
    return new IndentedExpression(style, expr);
  }
}