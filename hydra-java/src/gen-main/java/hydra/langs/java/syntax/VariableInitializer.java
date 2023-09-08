package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class VariableInitializer implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.VariableInitializer");
  
  private VariableInitializer () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Expression instance) ;
    
    R visit(ArrayInitializer instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(VariableInitializer instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Expression instance) {
      return otherwise((instance));
    }
    
    default R visit(ArrayInitializer instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Expression extends hydra.langs.java.syntax.VariableInitializer implements Serializable {
    public final hydra.langs.java.syntax.Expression value;
    
    public Expression (hydra.langs.java.syntax.Expression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Expression)) {
        return false;
      }
      Expression o = (Expression) (other);
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
  
  public static final class ArrayInitializer extends hydra.langs.java.syntax.VariableInitializer implements Serializable {
    public final hydra.langs.java.syntax.ArrayInitializer value;
    
    public ArrayInitializer (hydra.langs.java.syntax.ArrayInitializer value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ArrayInitializer)) {
        return false;
      }
      ArrayInitializer o = (ArrayInitializer) (other);
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