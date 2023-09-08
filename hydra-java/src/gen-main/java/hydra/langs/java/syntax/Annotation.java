package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class Annotation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Annotation");
  
  private Annotation () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Normal instance) ;
    
    R visit(Marker instance) ;
    
    R visit(SingleElement instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Annotation instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Normal instance) {
      return otherwise((instance));
    }
    
    default R visit(Marker instance) {
      return otherwise((instance));
    }
    
    default R visit(SingleElement instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Normal extends hydra.langs.java.syntax.Annotation implements Serializable {
    public final hydra.langs.java.syntax.NormalAnnotation value;
    
    public Normal (hydra.langs.java.syntax.NormalAnnotation value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Normal)) {
        return false;
      }
      Normal o = (Normal) (other);
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
  
  public static final class Marker extends hydra.langs.java.syntax.Annotation implements Serializable {
    public final hydra.langs.java.syntax.MarkerAnnotation value;
    
    public Marker (hydra.langs.java.syntax.MarkerAnnotation value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Marker)) {
        return false;
      }
      Marker o = (Marker) (other);
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
  
  public static final class SingleElement extends hydra.langs.java.syntax.Annotation implements Serializable {
    public final hydra.langs.java.syntax.SingleElementAnnotation value;
    
    public SingleElement (hydra.langs.java.syntax.SingleElementAnnotation value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SingleElement)) {
        return false;
      }
      SingleElement o = (SingleElement) (other);
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