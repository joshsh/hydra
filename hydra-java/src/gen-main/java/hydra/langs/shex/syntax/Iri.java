package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class Iri implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Iri");
  
  private Iri () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(IriRef instance) ;
    
    R visit(PrefixedName instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Iri instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(IriRef instance) {
      return otherwise((instance));
    }
    
    default R visit(PrefixedName instance) {
      return otherwise((instance));
    }
  }
  
  public static final class IriRef extends hydra.langs.shex.syntax.Iri implements Serializable {
    public final hydra.langs.shex.syntax.IriRef value;
    
    public IriRef (hydra.langs.shex.syntax.IriRef value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof IriRef)) {
        return false;
      }
      IriRef o = (IriRef) (other);
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
  
  public static final class PrefixedName extends hydra.langs.shex.syntax.Iri implements Serializable {
    public final hydra.langs.shex.syntax.PrefixedName value;
    
    public PrefixedName (hydra.langs.shex.syntax.PrefixedName value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof PrefixedName)) {
        return false;
      }
      PrefixedName o = (PrefixedName) (other);
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