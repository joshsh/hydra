package hydra.langs.java.syntax;

import java.io.Serializable;

public class SynchronizedStatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.SynchronizedStatement");
  
  public final hydra.langs.java.syntax.Expression expression;
  
  public final hydra.langs.java.syntax.Block block;
  
  public SynchronizedStatement (hydra.langs.java.syntax.Expression expression, hydra.langs.java.syntax.Block block) {
    this.expression = expression;
    this.block = block;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SynchronizedStatement)) {
      return false;
    }
    SynchronizedStatement o = (SynchronizedStatement) (other);
    return expression.equals(o.expression) && block.equals(o.block);
  }
  
  @Override
  public int hashCode() {
    return 2 * expression.hashCode() + 3 * block.hashCode();
  }
  
  public SynchronizedStatement withExpression(hydra.langs.java.syntax.Expression expression) {
    return new SynchronizedStatement(expression, block);
  }
  
  public SynchronizedStatement withBlock(hydra.langs.java.syntax.Block block) {
    return new SynchronizedStatement(expression, block);
  }
}