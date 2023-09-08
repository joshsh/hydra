package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class InterfaceDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.InterfaceDeclaration");
  
  private InterfaceDeclaration () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(NormalInterface instance) ;
    
    R visit(AnnotationType instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(InterfaceDeclaration instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(NormalInterface instance) {
      return otherwise((instance));
    }
    
    default R visit(AnnotationType instance) {
      return otherwise((instance));
    }
  }
  
  public static final class NormalInterface extends hydra.langs.java.syntax.InterfaceDeclaration implements Serializable {
    public final hydra.langs.java.syntax.NormalInterfaceDeclaration value;
    
    public NormalInterface (hydra.langs.java.syntax.NormalInterfaceDeclaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NormalInterface)) {
        return false;
      }
      NormalInterface o = (NormalInterface) (other);
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
  
  public static final class AnnotationType extends hydra.langs.java.syntax.InterfaceDeclaration implements Serializable {
    public final hydra.langs.java.syntax.AnnotationTypeDeclaration value;
    
    public AnnotationType (hydra.langs.java.syntax.AnnotationTypeDeclaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof AnnotationType)) {
        return false;
      }
      AnnotationType o = (AnnotationType) (other);
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