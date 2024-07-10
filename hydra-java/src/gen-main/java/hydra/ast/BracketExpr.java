// Note: this is an automatically generated file. Do not edit.

package hydra.ast;

import java.io.Serializable;

/**
 * An expression enclosed by brackets
 */
public class BracketExpr implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ast.BracketExpr");
  
  public final hydra.ast.Brackets brackets;
  
  public final hydra.ast.Expr enclosed;
  
  public final hydra.ast.BlockStyle style;
  
  public BracketExpr (hydra.ast.Brackets brackets, hydra.ast.Expr enclosed, hydra.ast.BlockStyle style) {
    if (brackets == null) {
      throw new IllegalArgumentException("null value for 'brackets' argument");
    }
    if (enclosed == null) {
      throw new IllegalArgumentException("null value for 'enclosed' argument");
    }
    if (style == null) {
      throw new IllegalArgumentException("null value for 'style' argument");
    }
    this.brackets = brackets;
    this.enclosed = enclosed;
    this.style = style;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BracketExpr)) {
      return false;
    }
    BracketExpr o = (BracketExpr) (other);
    return brackets.equals(o.brackets) && enclosed.equals(o.enclosed) && style.equals(o.style);
  }
  
  @Override
  public int hashCode() {
    return 2 * brackets.hashCode() + 3 * enclosed.hashCode() + 5 * style.hashCode();
  }
  
  public BracketExpr withBrackets(hydra.ast.Brackets brackets) {
    if (brackets == null) {
      throw new IllegalArgumentException("null value for 'brackets' argument");
    }
    return new BracketExpr(brackets, enclosed, style);
  }
  
  public BracketExpr withEnclosed(hydra.ast.Expr enclosed) {
    if (enclosed == null) {
      throw new IllegalArgumentException("null value for 'enclosed' argument");
    }
    return new BracketExpr(brackets, enclosed, style);
  }
  
  public BracketExpr withStyle(hydra.ast.BlockStyle style) {
    if (style == null) {
      throw new IllegalArgumentException("null value for 'style' argument");
    }
    return new BracketExpr(brackets, enclosed, style);
  }
}