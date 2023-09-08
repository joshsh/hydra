package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class PrefixedName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.PrefixedName");
  
  private PrefixedName () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(PnameLn instance) ;
    
    R visit(PnameNs instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(PrefixedName instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(PnameLn instance) {
      return otherwise((instance));
    }
    
    default R visit(PnameNs instance) {
      return otherwise((instance));
    }
  }
  
  public static final class PnameLn extends hydra.langs.shex.syntax.PrefixedName implements Serializable {
    public final hydra.langs.shex.syntax.PnameLn value;
    
    public PnameLn (hydra.langs.shex.syntax.PnameLn value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof PnameLn)) {
        return false;
      }
      PnameLn o = (PnameLn) (other);
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
  
  public static final class PnameNs extends hydra.langs.shex.syntax.PrefixedName implements Serializable {
    public final hydra.langs.shex.syntax.PnameNs value;
    
    public PnameNs (hydra.langs.shex.syntax.PnameNs value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof PnameNs)) {
        return false;
      }
      PnameNs o = (PnameNs) (other);
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