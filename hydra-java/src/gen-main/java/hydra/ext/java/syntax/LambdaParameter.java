package hydra.ext.java.syntax;

public abstract class LambdaParameter {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.LambdaParameter");
  
  private LambdaParameter () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Normal instance) ;
    
    R visit(VariableArity instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(LambdaParameter instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Normal instance) {
      return otherwise((instance));
    }
    
    default R visit(VariableArity instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Normal extends hydra.ext.java.syntax.LambdaParameter {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Normal");
    
    public final hydra.ext.java.syntax.LambdaParameter_Normal value;
    
    public Normal (hydra.ext.java.syntax.LambdaParameter_Normal value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Normal)) {
        return false;
      }
      Normal o = (Normal) (other);
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
  
  public static final class VariableArity extends hydra.ext.java.syntax.LambdaParameter {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.VariableArity");
    
    public final hydra.ext.java.syntax.VariableArityParameter value;
    
    public VariableArity (hydra.ext.java.syntax.VariableArityParameter value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof VariableArity)) {
        return false;
      }
      VariableArity o = (VariableArity) (other);
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