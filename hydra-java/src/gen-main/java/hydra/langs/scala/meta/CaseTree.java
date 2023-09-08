package hydra.langs.scala.meta;

import java.io.Serializable;

public abstract class CaseTree implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.CaseTree");
  
  private CaseTree () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Case instance) ;
    
    R visit(TypeCase instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(CaseTree instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Case instance) {
      return otherwise((instance));
    }
    
    default R visit(TypeCase instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Case extends hydra.langs.scala.meta.CaseTree implements Serializable {
    public final hydra.langs.scala.meta.Case value;
    
    public Case (hydra.langs.scala.meta.Case value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Case)) {
        return false;
      }
      Case o = (Case) (other);
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
  
  public static final class TypeCase extends hydra.langs.scala.meta.CaseTree implements Serializable {
    public final hydra.langs.scala.meta.TypeCase value;
    
    public TypeCase (hydra.langs.scala.meta.TypeCase value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof TypeCase)) {
        return false;
      }
      TypeCase o = (TypeCase) (other);
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