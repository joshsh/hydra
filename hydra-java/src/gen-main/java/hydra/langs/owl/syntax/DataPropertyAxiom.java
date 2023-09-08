package hydra.langs.owl.syntax;

import java.io.Serializable;

public abstract class DataPropertyAxiom implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataPropertyAxiom");
  
  private DataPropertyAxiom () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(DataPropertyAxiom_ instance) ;
    
    R visit(DataPropertyRange instance) ;
    
    R visit(DisjointDataProperties instance) ;
    
    R visit(EquivalentDataProperties instance) ;
    
    R visit(FunctionalDataProperty instance) ;
    
    R visit(SubDataPropertyOf instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(DataPropertyAxiom instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(DataPropertyAxiom_ instance) {
      return otherwise((instance));
    }
    
    default R visit(DataPropertyRange instance) {
      return otherwise((instance));
    }
    
    default R visit(DisjointDataProperties instance) {
      return otherwise((instance));
    }
    
    default R visit(EquivalentDataProperties instance) {
      return otherwise((instance));
    }
    
    default R visit(FunctionalDataProperty instance) {
      return otherwise((instance));
    }
    
    default R visit(SubDataPropertyOf instance) {
      return otherwise((instance));
    }
  }
  
  public static final class DataPropertyAxiom_ extends hydra.langs.owl.syntax.DataPropertyAxiom implements Serializable {
    public final hydra.langs.owl.syntax.DataPropertyAxiom value;
    
    public DataPropertyAxiom_ (hydra.langs.owl.syntax.DataPropertyAxiom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataPropertyAxiom_)) {
        return false;
      }
      DataPropertyAxiom_ o = (DataPropertyAxiom_) (other);
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
  
  public static final class DataPropertyRange extends hydra.langs.owl.syntax.DataPropertyAxiom implements Serializable {
    public final hydra.langs.owl.syntax.DataPropertyRange value;
    
    public DataPropertyRange (hydra.langs.owl.syntax.DataPropertyRange value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataPropertyRange)) {
        return false;
      }
      DataPropertyRange o = (DataPropertyRange) (other);
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
  
  public static final class DisjointDataProperties extends hydra.langs.owl.syntax.DataPropertyAxiom implements Serializable {
    public final hydra.langs.owl.syntax.DisjointDataProperties value;
    
    public DisjointDataProperties (hydra.langs.owl.syntax.DisjointDataProperties value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DisjointDataProperties)) {
        return false;
      }
      DisjointDataProperties o = (DisjointDataProperties) (other);
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
  
  public static final class EquivalentDataProperties extends hydra.langs.owl.syntax.DataPropertyAxiom implements Serializable {
    public final hydra.langs.owl.syntax.EquivalentDataProperties value;
    
    public EquivalentDataProperties (hydra.langs.owl.syntax.EquivalentDataProperties value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof EquivalentDataProperties)) {
        return false;
      }
      EquivalentDataProperties o = (EquivalentDataProperties) (other);
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
  
  public static final class FunctionalDataProperty extends hydra.langs.owl.syntax.DataPropertyAxiom implements Serializable {
    public final hydra.langs.owl.syntax.FunctionalDataProperty value;
    
    public FunctionalDataProperty (hydra.langs.owl.syntax.FunctionalDataProperty value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof FunctionalDataProperty)) {
        return false;
      }
      FunctionalDataProperty o = (FunctionalDataProperty) (other);
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
  
  public static final class SubDataPropertyOf extends hydra.langs.owl.syntax.DataPropertyAxiom implements Serializable {
    public final hydra.langs.owl.syntax.SubDataPropertyOf value;
    
    public SubDataPropertyOf (hydra.langs.owl.syntax.SubDataPropertyOf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SubDataPropertyOf)) {
        return false;
      }
      SubDataPropertyOf o = (SubDataPropertyOf) (other);
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