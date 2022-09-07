package hydra.ext.java.syntax;

public abstract class InterfaceModifier {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.InterfaceModifier");
  
  private InterfaceModifier () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Annotation instance) ;
    
    R visit(Public instance) ;
    
    R visit(Protected instance) ;
    
    R visit(Private instance) ;
    
    R visit(Abstract instance) ;
    
    R visit(Static instance) ;
    
    R visit(Strictfb instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(InterfaceModifier instance) {
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
    
    default R visit(Abstract instance) {
      return otherwise((instance));
    }
    
    default R visit(Static instance) {
      return otherwise((instance));
    }
    
    default R visit(Strictfb instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Annotation extends hydra.ext.java.syntax.InterfaceModifier {
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
  
  public static final class Public extends hydra.ext.java.syntax.InterfaceModifier {
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
  
  public static final class Protected extends hydra.ext.java.syntax.InterfaceModifier {
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
  
  public static final class Private extends hydra.ext.java.syntax.InterfaceModifier {
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
  
  public static final class Abstract extends hydra.ext.java.syntax.InterfaceModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Abstract");
    
    public Abstract () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Abstract)) {
        return false;
      }
      Abstract o = (Abstract) (other);
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
  
  public static final class Static extends hydra.ext.java.syntax.InterfaceModifier {
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
  
  public static final class Strictfb extends hydra.ext.java.syntax.InterfaceModifier {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.Strictfb");
    
    public Strictfb () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Strictfb)) {
        return false;
      }
      Strictfb o = (Strictfb) (other);
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