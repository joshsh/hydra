package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * The 'data' versus 'newtype keyword
 */
public abstract class DataDeclaration_Keyword implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.DataDeclaration.Keyword");
  
  private DataDeclaration_Keyword () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Data instance) ;
    
    R visit(Newtype instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(DataDeclaration_Keyword instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Data instance) {
      return otherwise((instance));
    }
    
    default R visit(Newtype instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Data extends hydra.langs.haskell.ast.DataDeclaration_Keyword implements Serializable {
    public Data () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Data)) {
        return false;
      }
      Data o = (Data) (other);
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
  
  public static final class Newtype extends hydra.langs.haskell.ast.DataDeclaration_Keyword implements Serializable {
    public Newtype () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Newtype)) {
        return false;
      }
      Newtype o = (Newtype) (other);
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