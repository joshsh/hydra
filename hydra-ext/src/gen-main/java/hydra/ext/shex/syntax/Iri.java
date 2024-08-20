// Note: this is an automatically generated file. Do not edit.

package hydra.ext.shex.syntax;

import java.io.Serializable;

public abstract class Iri implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/ext/shex/syntax.Iri");
  
  public static final hydra.core.Name FIELD_NAME_IRI_REF = new hydra.core.Name("iriRef");
  
  public static final hydra.core.Name FIELD_NAME_PREFIXED_NAME = new hydra.core.Name("prefixedName");
  
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
  
  public static final class IriRef extends hydra.ext.shex.syntax.Iri implements Serializable {
    public final hydra.ext.shex.syntax.IriRef value;
    
    public IriRef (hydra.ext.shex.syntax.IriRef value) {
      java.util.Objects.requireNonNull((value));
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
  
  public static final class PrefixedName extends hydra.ext.shex.syntax.Iri implements Serializable {
    public final hydra.ext.shex.syntax.PrefixedName value;
    
    public PrefixedName (hydra.ext.shex.syntax.PrefixedName value) {
      java.util.Objects.requireNonNull((value));
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