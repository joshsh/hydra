package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class ForInit implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ForInit");
  
  private ForInit () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Statements instance) ;
    
    R visit(LocalVariable instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ForInit instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Statements instance) {
      return otherwise((instance));
    }
    
    default R visit(LocalVariable instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Statements extends hydra.langs.java.syntax.ForInit implements Serializable {
    public final java.util.List<hydra.langs.java.syntax.StatementExpression> value;
    
    public Statements (java.util.List<hydra.langs.java.syntax.StatementExpression> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Statements)) {
        return false;
      }
      Statements o = (Statements) (other);
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
  
  public static final class LocalVariable extends hydra.langs.java.syntax.ForInit implements Serializable {
    public final hydra.langs.java.syntax.LocalVariableDeclaration value;
    
    public LocalVariable (hydra.langs.java.syntax.LocalVariableDeclaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof LocalVariable)) {
        return false;
      }
      LocalVariable o = (LocalVariable) (other);
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