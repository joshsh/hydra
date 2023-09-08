package hydra.langs.owl.syntax;

import java.io.Serializable;

public abstract class Entity implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.Entity");
  
  private Entity () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(AnnotationProperty instance) ;
    
    R visit(Class_ instance) ;
    
    R visit(DataProperty instance) ;
    
    R visit(Datatype instance) ;
    
    R visit(NamedIndividual instance) ;
    
    R visit(ObjectProperty instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Entity instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(AnnotationProperty instance) {
      return otherwise((instance));
    }
    
    default R visit(Class_ instance) {
      return otherwise((instance));
    }
    
    default R visit(DataProperty instance) {
      return otherwise((instance));
    }
    
    default R visit(Datatype instance) {
      return otherwise((instance));
    }
    
    default R visit(NamedIndividual instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectProperty instance) {
      return otherwise((instance));
    }
  }
  
  public static final class AnnotationProperty extends hydra.langs.owl.syntax.Entity implements Serializable {
    public final hydra.langs.owl.syntax.AnnotationProperty value;
    
    public AnnotationProperty (hydra.langs.owl.syntax.AnnotationProperty value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof AnnotationProperty)) {
        return false;
      }
      AnnotationProperty o = (AnnotationProperty) (other);
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
  
  public static final class Class_ extends hydra.langs.owl.syntax.Entity implements Serializable {
    public final hydra.langs.owl.syntax.Class_ value;
    
    public Class_ (hydra.langs.owl.syntax.Class_ value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Class_)) {
        return false;
      }
      Class_ o = (Class_) (other);
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
  
  public static final class DataProperty extends hydra.langs.owl.syntax.Entity implements Serializable {
    public final hydra.langs.owl.syntax.DataProperty value;
    
    public DataProperty (hydra.langs.owl.syntax.DataProperty value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataProperty)) {
        return false;
      }
      DataProperty o = (DataProperty) (other);
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
  
  public static final class Datatype extends hydra.langs.owl.syntax.Entity implements Serializable {
    public final hydra.langs.owl.syntax.Datatype value;
    
    public Datatype (hydra.langs.owl.syntax.Datatype value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Datatype)) {
        return false;
      }
      Datatype o = (Datatype) (other);
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
  
  public static final class NamedIndividual extends hydra.langs.owl.syntax.Entity implements Serializable {
    public final hydra.langs.owl.syntax.NamedIndividual value;
    
    public NamedIndividual (hydra.langs.owl.syntax.NamedIndividual value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NamedIndividual)) {
        return false;
      }
      NamedIndividual o = (NamedIndividual) (other);
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
  
  public static final class ObjectProperty extends hydra.langs.owl.syntax.Entity implements Serializable {
    public final hydra.langs.owl.syntax.ObjectProperty value;
    
    public ObjectProperty (hydra.langs.owl.syntax.ObjectProperty value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectProperty)) {
        return false;
      }
      ObjectProperty o = (ObjectProperty) (other);
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