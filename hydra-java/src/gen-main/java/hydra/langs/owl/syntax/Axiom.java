package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Axioms
 */
public abstract class Axiom implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.Axiom");
  
  private Axiom () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(AnnotationAxiom instance) ;
    
    R visit(Assertion instance) ;
    
    R visit(ClassAxiom instance) ;
    
    R visit(DataPropertyAxiom instance) ;
    
    R visit(DatatypeDefinition instance) ;
    
    R visit(Declaration instance) ;
    
    R visit(HasKey instance) ;
    
    R visit(ObjectPropertyAxiom instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Axiom instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(AnnotationAxiom instance) {
      return otherwise((instance));
    }
    
    default R visit(Assertion instance) {
      return otherwise((instance));
    }
    
    default R visit(ClassAxiom instance) {
      return otherwise((instance));
    }
    
    default R visit(DataPropertyAxiom instance) {
      return otherwise((instance));
    }
    
    default R visit(DatatypeDefinition instance) {
      return otherwise((instance));
    }
    
    default R visit(Declaration instance) {
      return otherwise((instance));
    }
    
    default R visit(HasKey instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectPropertyAxiom instance) {
      return otherwise((instance));
    }
  }
  
  public static final class AnnotationAxiom extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.AnnotationAxiom value;
    
    public AnnotationAxiom (hydra.langs.owl.syntax.AnnotationAxiom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof AnnotationAxiom)) {
        return false;
      }
      AnnotationAxiom o = (AnnotationAxiom) (other);
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
  
  public static final class Assertion extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.Assertion value;
    
    public Assertion (hydra.langs.owl.syntax.Assertion value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Assertion)) {
        return false;
      }
      Assertion o = (Assertion) (other);
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
  
  public static final class ClassAxiom extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.ClassAxiom value;
    
    public ClassAxiom (hydra.langs.owl.syntax.ClassAxiom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ClassAxiom)) {
        return false;
      }
      ClassAxiom o = (ClassAxiom) (other);
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
  
  public static final class DataPropertyAxiom extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.DataPropertyAxiom value;
    
    public DataPropertyAxiom (hydra.langs.owl.syntax.DataPropertyAxiom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataPropertyAxiom)) {
        return false;
      }
      DataPropertyAxiom o = (DataPropertyAxiom) (other);
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
  
  public static final class DatatypeDefinition extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.DatatypeDefinition value;
    
    public DatatypeDefinition (hydra.langs.owl.syntax.DatatypeDefinition value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DatatypeDefinition)) {
        return false;
      }
      DatatypeDefinition o = (DatatypeDefinition) (other);
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
  
  public static final class Declaration extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.Declaration value;
    
    public Declaration (hydra.langs.owl.syntax.Declaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Declaration)) {
        return false;
      }
      Declaration o = (Declaration) (other);
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
  
  public static final class HasKey extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.HasKey value;
    
    public HasKey (hydra.langs.owl.syntax.HasKey value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof HasKey)) {
        return false;
      }
      HasKey o = (HasKey) (other);
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
  
  public static final class ObjectPropertyAxiom extends hydra.langs.owl.syntax.Axiom implements Serializable {
    public final hydra.langs.owl.syntax.ObjectPropertyAxiom value;
    
    public ObjectPropertyAxiom (hydra.langs.owl.syntax.ObjectPropertyAxiom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectPropertyAxiom)) {
        return false;
      }
      ObjectPropertyAxiom o = (ObjectPropertyAxiom) (other);
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