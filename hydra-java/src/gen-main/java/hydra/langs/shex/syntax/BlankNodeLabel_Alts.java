package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class BlankNodeLabel_Alts implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.BlankNodeLabel.Alts");
  
  private BlankNodeLabel_Alts () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(PnCharsU instance) ;
    
    R visit(Regex instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(BlankNodeLabel_Alts instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(PnCharsU instance) {
      return otherwise((instance));
    }
    
    default R visit(Regex instance) {
      return otherwise((instance));
    }
  }
  
  public static final class PnCharsU extends hydra.langs.shex.syntax.BlankNodeLabel_Alts implements Serializable {
    public final hydra.langs.shex.syntax.PnCharsU value;
    
    public PnCharsU (hydra.langs.shex.syntax.PnCharsU value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof PnCharsU)) {
        return false;
      }
      PnCharsU o = (PnCharsU) (other);
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
  
  public static final class Regex extends hydra.langs.shex.syntax.BlankNodeLabel_Alts implements Serializable {
    public final String value;
    
    public Regex (String value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Regex)) {
        return false;
      }
      Regex o = (Regex) (other);
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