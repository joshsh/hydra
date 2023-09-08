package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class Primary implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Primary");
  
  private Primary () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(NoNewArray instance) ;
    
    R visit(ArrayCreation instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Primary instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(NoNewArray instance) {
      return otherwise((instance));
    }
    
    default R visit(ArrayCreation instance) {
      return otherwise((instance));
    }
  }
  
  public static final class NoNewArray extends hydra.langs.java.syntax.Primary implements Serializable {
    public final hydra.langs.java.syntax.PrimaryNoNewArray value;
    
    public NoNewArray (hydra.langs.java.syntax.PrimaryNoNewArray value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NoNewArray)) {
        return false;
      }
      NoNewArray o = (NoNewArray) (other);
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
  
  public static final class ArrayCreation extends hydra.langs.java.syntax.Primary implements Serializable {
    public final hydra.langs.java.syntax.ArrayCreationExpression value;
    
    public ArrayCreation (hydra.langs.java.syntax.ArrayCreationExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ArrayCreation)) {
        return false;
      }
      ArrayCreation o = (ArrayCreation) (other);
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