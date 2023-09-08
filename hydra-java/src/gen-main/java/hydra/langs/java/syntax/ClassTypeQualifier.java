package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class ClassTypeQualifier implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ClassTypeQualifier");
  
  private ClassTypeQualifier () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(None instance) ;
    
    R visit(Package_ instance) ;
    
    R visit(Parent instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ClassTypeQualifier instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(None instance) {
      return otherwise((instance));
    }
    
    default R visit(Package_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Parent instance) {
      return otherwise((instance));
    }
  }
  
  public static final class None extends hydra.langs.java.syntax.ClassTypeQualifier implements Serializable {
    public None () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof None)) {
        return false;
      }
      None o = (None) (other);
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
  
  public static final class Package_ extends hydra.langs.java.syntax.ClassTypeQualifier implements Serializable {
    public final hydra.langs.java.syntax.PackageName value;
    
    public Package_ (hydra.langs.java.syntax.PackageName value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Package_)) {
        return false;
      }
      Package_ o = (Package_) (other);
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
  
  public static final class Parent extends hydra.langs.java.syntax.ClassTypeQualifier implements Serializable {
    public final hydra.langs.java.syntax.ClassOrInterfaceType value;
    
    public Parent (hydra.langs.java.syntax.ClassOrInterfaceType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Parent)) {
        return false;
      }
      Parent o = (Parent) (other);
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