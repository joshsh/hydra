package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class PnCharsU implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.PnCharsU");
  
  private PnCharsU () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(PnCharsBase instance) ;
    
    R visit(Lowbar instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(PnCharsU instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(PnCharsBase instance) {
      return otherwise((instance));
    }
    
    default R visit(Lowbar instance) {
      return otherwise((instance));
    }
  }
  
  public static final class PnCharsBase extends hydra.langs.shex.syntax.PnCharsU implements Serializable {
    public final hydra.langs.shex.syntax.PnCharsBase value;
    
    public PnCharsBase (hydra.langs.shex.syntax.PnCharsBase value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof PnCharsBase)) {
        return false;
      }
      PnCharsBase o = (PnCharsBase) (other);
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
  
  public static final class Lowbar extends hydra.langs.shex.syntax.PnCharsU implements Serializable {
    public Lowbar () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Lowbar)) {
        return false;
      }
      Lowbar o = (Lowbar) (other);
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