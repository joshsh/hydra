package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class CodeDecl_Alts implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.CodeDecl.Alts");
  
  private CodeDecl_Alts () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Code instance) ;
    
    R visit(Percnt instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(CodeDecl_Alts instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Code instance) {
      return otherwise((instance));
    }
    
    default R visit(Percnt instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Code extends hydra.langs.shex.syntax.CodeDecl_Alts implements Serializable {
    public final hydra.langs.shex.syntax.Code value;
    
    public Code (hydra.langs.shex.syntax.Code value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Code)) {
        return false;
      }
      Code o = (Code) (other);
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
  
  public static final class Percnt extends hydra.langs.shex.syntax.CodeDecl_Alts implements Serializable {
    public Percnt () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Percnt)) {
        return false;
      }
      Percnt o = (Percnt) (other);
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