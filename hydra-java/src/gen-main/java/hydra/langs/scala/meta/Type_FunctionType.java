package hydra.langs.scala.meta;

import java.io.Serializable;

public abstract class Type_FunctionType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.FunctionType");
  
  private Type_FunctionType () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Function instance) ;
    
    R visit(ContextFunction instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Type_FunctionType instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Function instance) {
      return otherwise((instance));
    }
    
    default R visit(ContextFunction instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Function extends hydra.langs.scala.meta.Type_FunctionType implements Serializable {
    public final hydra.langs.scala.meta.Type_Function value;
    
    public Function (hydra.langs.scala.meta.Type_Function value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Function)) {
        return false;
      }
      Function o = (Function) (other);
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
  
  public static final class ContextFunction extends hydra.langs.scala.meta.Type_FunctionType implements Serializable {
    public final hydra.langs.scala.meta.Type_ContextFunction value;
    
    public ContextFunction (hydra.langs.scala.meta.Type_ContextFunction value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ContextFunction)) {
        return false;
      }
      ContextFunction o = (ContextFunction) (other);
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