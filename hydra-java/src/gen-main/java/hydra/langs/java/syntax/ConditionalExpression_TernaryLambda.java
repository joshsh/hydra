package hydra.langs.java.syntax;

import java.io.Serializable;

public class ConditionalExpression_TernaryLambda implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ConditionalExpression.TernaryLambda");
  
  public final hydra.langs.java.syntax.ConditionalOrExpression cond;
  
  public final hydra.langs.java.syntax.Expression ifTrue;
  
  public final hydra.langs.java.syntax.LambdaExpression ifFalse;
  
  public ConditionalExpression_TernaryLambda (hydra.langs.java.syntax.ConditionalOrExpression cond, hydra.langs.java.syntax.Expression ifTrue, hydra.langs.java.syntax.LambdaExpression ifFalse) {
    this.cond = cond;
    this.ifTrue = ifTrue;
    this.ifFalse = ifFalse;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ConditionalExpression_TernaryLambda)) {
      return false;
    }
    ConditionalExpression_TernaryLambda o = (ConditionalExpression_TernaryLambda) (other);
    return cond.equals(o.cond) && ifTrue.equals(o.ifTrue) && ifFalse.equals(o.ifFalse);
  }
  
  @Override
  public int hashCode() {
    return 2 * cond.hashCode() + 3 * ifTrue.hashCode() + 5 * ifFalse.hashCode();
  }
  
  public ConditionalExpression_TernaryLambda withCond(hydra.langs.java.syntax.ConditionalOrExpression cond) {
    return new ConditionalExpression_TernaryLambda(cond, ifTrue, ifFalse);
  }
  
  public ConditionalExpression_TernaryLambda withIfTrue(hydra.langs.java.syntax.Expression ifTrue) {
    return new ConditionalExpression_TernaryLambda(cond, ifTrue, ifFalse);
  }
  
  public ConditionalExpression_TernaryLambda withIfFalse(hydra.langs.java.syntax.LambdaExpression ifFalse) {
    return new ConditionalExpression_TernaryLambda(cond, ifTrue, ifFalse);
  }
}