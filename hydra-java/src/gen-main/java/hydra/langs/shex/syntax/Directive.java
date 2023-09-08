package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class Directive implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Directive");
  
  private Directive () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(BaseDecl instance) ;
    
    R visit(PrefixDecl instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Directive instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(BaseDecl instance) {
      return otherwise((instance));
    }
    
    default R visit(PrefixDecl instance) {
      return otherwise((instance));
    }
  }
  
  public static final class BaseDecl extends hydra.langs.shex.syntax.Directive implements Serializable {
    public final hydra.langs.shex.syntax.BaseDecl value;
    
    public BaseDecl (hydra.langs.shex.syntax.BaseDecl value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof BaseDecl)) {
        return false;
      }
      BaseDecl o = (BaseDecl) (other);
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
  
  public static final class PrefixDecl extends hydra.langs.shex.syntax.Directive implements Serializable {
    public final hydra.langs.shex.syntax.PrefixDecl value;
    
    public PrefixDecl (hydra.langs.shex.syntax.PrefixDecl value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof PrefixDecl)) {
        return false;
      }
      PrefixDecl o = (PrefixDecl) (other);
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