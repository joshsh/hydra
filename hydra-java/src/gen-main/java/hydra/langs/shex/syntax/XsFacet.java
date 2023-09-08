package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class XsFacet implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.XsFacet");
  
  private XsFacet () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(StringFacet instance) ;
    
    R visit(NumericFacet instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(XsFacet instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(StringFacet instance) {
      return otherwise((instance));
    }
    
    default R visit(NumericFacet instance) {
      return otherwise((instance));
    }
  }
  
  public static final class StringFacet extends hydra.langs.shex.syntax.XsFacet implements Serializable {
    public final hydra.langs.shex.syntax.StringFacet value;
    
    public StringFacet (hydra.langs.shex.syntax.StringFacet value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof StringFacet)) {
        return false;
      }
      StringFacet o = (StringFacet) (other);
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
  
  public static final class NumericFacet extends hydra.langs.shex.syntax.XsFacet implements Serializable {
    public final hydra.langs.shex.syntax.NumericFacet value;
    
    public NumericFacet (hydra.langs.shex.syntax.NumericFacet value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NumericFacet)) {
        return false;
      }
      NumericFacet o = (NumericFacet) (other);
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