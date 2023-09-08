package hydra.langs.java.syntax;

import java.io.Serializable;

public class Assignment implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Assignment");
  
  public final hydra.langs.java.syntax.LeftHandSide lhs;
  
  public final hydra.langs.java.syntax.AssignmentOperator op;
  
  public final hydra.langs.java.syntax.Expression expression;
  
  public Assignment (hydra.langs.java.syntax.LeftHandSide lhs, hydra.langs.java.syntax.AssignmentOperator op, hydra.langs.java.syntax.Expression expression) {
    this.lhs = lhs;
    this.op = op;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Assignment)) {
      return false;
    }
    Assignment o = (Assignment) (other);
    return lhs.equals(o.lhs) && op.equals(o.op) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * op.hashCode() + 5 * expression.hashCode();
  }
  
  public Assignment withLhs(hydra.langs.java.syntax.LeftHandSide lhs) {
    return new Assignment(lhs, op, expression);
  }
  
  public Assignment withOp(hydra.langs.java.syntax.AssignmentOperator op) {
    return new Assignment(lhs, op, expression);
  }
  
  public Assignment withExpression(hydra.langs.java.syntax.Expression expression) {
    return new Assignment(lhs, op, expression);
  }
}