package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * An import specification
 */
public abstract class Import_Spec implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Import.Spec");
  
  private Import_Spec () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(List instance) ;
    
    R visit(Hiding instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Import_Spec instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(List instance) {
      return otherwise((instance));
    }
    
    default R visit(Hiding instance) {
      return otherwise((instance));
    }
  }
  
  public static final class List extends hydra.langs.haskell.ast.Import_Spec implements Serializable {
    public final java.util.List<hydra.langs.haskell.ast.ImportExportSpec> value;
    
    public List (java.util.List<hydra.langs.haskell.ast.ImportExportSpec> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof List)) {
        return false;
      }
      List o = (List) (other);
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
  
  public static final class Hiding extends hydra.langs.haskell.ast.Import_Spec implements Serializable {
    public final java.util.List<hydra.langs.haskell.ast.ImportExportSpec> value;
    
    public Hiding (java.util.List<hydra.langs.haskell.ast.ImportExportSpec> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Hiding)) {
        return false;
      }
      Hiding o = (Hiding) (other);
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