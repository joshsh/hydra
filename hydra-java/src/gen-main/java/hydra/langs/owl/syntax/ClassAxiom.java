package hydra.langs.owl.syntax;

import java.io.Serializable;

public abstract class ClassAxiom implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ClassAxiom");
  
  private ClassAxiom () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(DisjointClasses instance) ;
    
    R visit(DisjointUnion instance) ;
    
    R visit(EquivalentClasses instance) ;
    
    R visit(SubClassOf instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ClassAxiom instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(DisjointClasses instance) {
      return otherwise((instance));
    }
    
    default R visit(DisjointUnion instance) {
      return otherwise((instance));
    }
    
    default R visit(EquivalentClasses instance) {
      return otherwise((instance));
    }
    
    default R visit(SubClassOf instance) {
      return otherwise((instance));
    }
  }
  
  public static final class DisjointClasses extends hydra.langs.owl.syntax.ClassAxiom implements Serializable {
    public final hydra.langs.owl.syntax.DisjointClasses value;
    
    public DisjointClasses (hydra.langs.owl.syntax.DisjointClasses value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DisjointClasses)) {
        return false;
      }
      DisjointClasses o = (DisjointClasses) (other);
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
  
  public static final class DisjointUnion extends hydra.langs.owl.syntax.ClassAxiom implements Serializable {
    public final hydra.langs.owl.syntax.DisjointUnion value;
    
    public DisjointUnion (hydra.langs.owl.syntax.DisjointUnion value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DisjointUnion)) {
        return false;
      }
      DisjointUnion o = (DisjointUnion) (other);
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
  
  public static final class EquivalentClasses extends hydra.langs.owl.syntax.ClassAxiom implements Serializable {
    public final hydra.langs.owl.syntax.EquivalentClasses value;
    
    public EquivalentClasses (hydra.langs.owl.syntax.EquivalentClasses value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof EquivalentClasses)) {
        return false;
      }
      EquivalentClasses o = (EquivalentClasses) (other);
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
  
  public static final class SubClassOf extends hydra.langs.owl.syntax.ClassAxiom implements Serializable {
    public final hydra.langs.owl.syntax.SubClassOf value;
    
    public SubClassOf (hydra.langs.owl.syntax.SubClassOf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SubClassOf)) {
        return false;
      }
      SubClassOf o = (SubClassOf) (other);
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