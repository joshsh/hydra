package hydra.ext.java.syntax;

public abstract class FieldModifier {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.FieldModifier");
  
  private FieldModifier () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Annotation instance) ;
    
    R visit(Public instance) ;
    
    R visit(Protected instance) ;
    
    R visit(Private instance) ;
    
    R visit(Static instance) ;
    
    R visit(Final instance) ;
    
    R visit(Transient instance) ;
    
    R visit(Volatile instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(FieldModifier instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Annotation instance) {
      return otherwise((instance));
    }
    
    default R visit(Public instance) {
      return otherwise((instance));
    }
    
    default R visit(Protected instance) {
      return otherwise((instance));
    }
    
    default R visit(Private instance) {
      return otherwise((instance));
    }
    
    default R visit(Static instance) {
      return otherwise((instance));
    }
    
    default R visit(Final instance) {
      return otherwise((instance));
    }
    
    default R visit(Transient instance) {
      return otherwise((instance));
    }
    
    default R visit(Volatile instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Annotation extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Annotation");
    
    public final hydra.ext.java.syntax.Annotation value;
    
    public Annotation (hydra.ext.java.syntax.Annotation value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Annotation)) {
        return false;
      }
      Annotation o = (Annotation) (other);
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
  
  public static final class Public extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Public");
    
    public Public () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Public)) {
        return false;
      }
      Public o = (Public) (other);
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
  
  public static final class Protected extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Protected");
    
    public Protected () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Protected)) {
        return false;
      }
      Protected o = (Protected) (other);
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
  
  public static final class Private extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Private");
    
    public Private () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Private)) {
        return false;
      }
      Private o = (Private) (other);
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
  
  public static final class Static extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Static");
    
    public Static () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Static)) {
        return false;
      }
      Static o = (Static) (other);
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
  
  public static final class Final extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Final");
    
    public Final () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Final)) {
        return false;
      }
      Final o = (Final) (other);
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
  
  public static final class Transient extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Transient");
    
    public Transient () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Transient)) {
        return false;
      }
      Transient o = (Transient) (other);
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
  
  public static final class Volatile extends hydra.ext.java.syntax.FieldModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Volatile");
    
    public Volatile () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Volatile)) {
        return false;
      }
      Volatile o = (Volatile) (other);
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
}