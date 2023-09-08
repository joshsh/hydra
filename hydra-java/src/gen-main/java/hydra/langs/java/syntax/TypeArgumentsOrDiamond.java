package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class TypeArgumentsOrDiamond implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TypeArgumentsOrDiamond");
  
  private TypeArgumentsOrDiamond () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Arguments instance) ;
    
    R visit(Diamond instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TypeArgumentsOrDiamond instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Arguments instance) {
      return otherwise((instance));
    }
    
    default R visit(Diamond instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Arguments extends hydra.langs.java.syntax.TypeArgumentsOrDiamond implements Serializable {
    public final java.util.List<hydra.langs.java.syntax.TypeArgument> value;
    
    public Arguments (java.util.List<hydra.langs.java.syntax.TypeArgument> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Arguments)) {
        return false;
      }
      Arguments o = (Arguments) (other);
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
  
  public static final class Diamond extends hydra.langs.java.syntax.TypeArgumentsOrDiamond implements Serializable {
    public Diamond () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Diamond)) {
        return false;
      }
      Diamond o = (Diamond) (other);
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