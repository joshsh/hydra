package hydra.langs.haskell.ast;

import java.io.Serializable;

public abstract class Operator implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Operator");
  
  private Operator () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Backtick instance) ;
    
    R visit(Normal instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Operator instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Backtick instance) {
      return otherwise((instance));
    }
    
    default R visit(Normal instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Backtick extends hydra.langs.haskell.ast.Operator implements Serializable {
    public final hydra.langs.haskell.ast.QualifiedName value;
    
    public Backtick (hydra.langs.haskell.ast.QualifiedName value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Backtick)) {
        return false;
      }
      Backtick o = (Backtick) (other);
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
  
  public static final class Normal extends hydra.langs.haskell.ast.Operator implements Serializable {
    public final hydra.langs.haskell.ast.QualifiedName value;
    
    public Normal (hydra.langs.haskell.ast.QualifiedName value) {
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
}