package hydra.langs.owl.syntax;

import java.io.Serializable;

public abstract class Assertion implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.Assertion");
  
  private Assertion () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(ClassAssertion instance) ;
    
    R visit(DataPropertyAssertion instance) ;
    
    R visit(DifferentIndividuals instance) ;
    
    R visit(ObjectPropertyAssertion instance) ;
    
    R visit(NegativeDataPropertyAssertion instance) ;
    
    R visit(NegativeObjectPropertyAssertion instance) ;
    
    R visit(SameIndividual instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Assertion instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(ClassAssertion instance) {
      return otherwise((instance));
    }
    
    default R visit(DataPropertyAssertion instance) {
      return otherwise((instance));
    }
    
    default R visit(DifferentIndividuals instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectPropertyAssertion instance) {
      return otherwise((instance));
    }
    
    default R visit(NegativeDataPropertyAssertion instance) {
      return otherwise((instance));
    }
    
    default R visit(NegativeObjectPropertyAssertion instance) {
      return otherwise((instance));
    }
    
    default R visit(SameIndividual instance) {
      return otherwise((instance));
    }
  }
  
  public static final class ClassAssertion extends hydra.langs.owl.syntax.Assertion implements Serializable {
    public final hydra.langs.owl.syntax.ClassAssertion value;
    
    public ClassAssertion (hydra.langs.owl.syntax.ClassAssertion value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ClassAssertion)) {
        return false;
      }
      ClassAssertion o = (ClassAssertion) (other);
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
  
  public static final class DataPropertyAssertion extends hydra.langs.owl.syntax.Assertion implements Serializable {
    public final hydra.langs.owl.syntax.DataPropertyAssertion value;
    
    public DataPropertyAssertion (hydra.langs.owl.syntax.DataPropertyAssertion value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataPropertyAssertion)) {
        return false;
      }
      DataPropertyAssertion o = (DataPropertyAssertion) (other);
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
  
  public static final class DifferentIndividuals extends hydra.langs.owl.syntax.Assertion implements Serializable {
    public final hydra.langs.owl.syntax.DifferentIndividuals value;
    
    public DifferentIndividuals (hydra.langs.owl.syntax.DifferentIndividuals value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DifferentIndividuals)) {
        return false;
      }
      DifferentIndividuals o = (DifferentIndividuals) (other);
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
  
  public static final class ObjectPropertyAssertion extends hydra.langs.owl.syntax.Assertion implements Serializable {
    public final hydra.langs.owl.syntax.ObjectPropertyAssertion value;
    
    public ObjectPropertyAssertion (hydra.langs.owl.syntax.ObjectPropertyAssertion value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectPropertyAssertion)) {
        return false;
      }
      ObjectPropertyAssertion o = (ObjectPropertyAssertion) (other);
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
  
  public static final class NegativeDataPropertyAssertion extends hydra.langs.owl.syntax.Assertion implements Serializable {
    public final hydra.langs.owl.syntax.NegativeDataPropertyAssertion value;
    
    public NegativeDataPropertyAssertion (hydra.langs.owl.syntax.NegativeDataPropertyAssertion value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NegativeDataPropertyAssertion)) {
        return false;
      }
      NegativeDataPropertyAssertion o = (NegativeDataPropertyAssertion) (other);
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
  
  public static final class NegativeObjectPropertyAssertion extends hydra.langs.owl.syntax.Assertion implements Serializable {
    public final hydra.langs.owl.syntax.NegativeObjectPropertyAssertion value;
    
    public NegativeObjectPropertyAssertion (hydra.langs.owl.syntax.NegativeObjectPropertyAssertion value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NegativeObjectPropertyAssertion)) {
        return false;
      }
      NegativeObjectPropertyAssertion o = (NegativeObjectPropertyAssertion) (other);
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
  
  public static final class SameIndividual extends hydra.langs.owl.syntax.Assertion implements Serializable {
    public final hydra.langs.owl.syntax.SameIndividual value;
    
    public SameIndividual (hydra.langs.owl.syntax.SameIndividual value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SameIndividual)) {
        return false;
      }
      SameIndividual o = (SameIndividual) (other);
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