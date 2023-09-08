package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class RdfLiteral_Alts_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.RdfLiteral.Alts.Option");
  
  private RdfLiteral_Alts_Option () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(LangTag instance) ;
    
    R visit(Sequence instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(RdfLiteral_Alts_Option instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(LangTag instance) {
      return otherwise((instance));
    }
    
    default R visit(Sequence instance) {
      return otherwise((instance));
    }
  }
  
  public static final class LangTag extends hydra.langs.shex.syntax.RdfLiteral_Alts_Option implements Serializable {
    public final hydra.langs.shex.syntax.LangTag value;
    
    public LangTag (hydra.langs.shex.syntax.LangTag value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof LangTag)) {
        return false;
      }
      LangTag o = (LangTag) (other);
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
  
  public static final class Sequence extends hydra.langs.shex.syntax.RdfLiteral_Alts_Option implements Serializable {
    public final hydra.langs.shex.syntax.Datatype value;
    
    public Sequence (hydra.langs.shex.syntax.Datatype value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sequence)) {
        return false;
      }
      Sequence o = (Sequence) (other);
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