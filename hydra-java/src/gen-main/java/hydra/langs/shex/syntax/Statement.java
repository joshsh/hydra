package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class Statement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Statement");
  
  private Statement () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Directive instance) ;
    
    R visit(NotStartAction instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Statement instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Directive instance) {
      return otherwise((instance));
    }
    
    default R visit(NotStartAction instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Directive extends hydra.langs.shex.syntax.Statement implements Serializable {
    public final hydra.langs.shex.syntax.Directive value;
    
    public Directive (hydra.langs.shex.syntax.Directive value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Directive)) {
        return false;
      }
      Directive o = (Directive) (other);
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
  
  public static final class NotStartAction extends hydra.langs.shex.syntax.Statement implements Serializable {
    public final hydra.langs.shex.syntax.NotStartAction value;
    
    public NotStartAction (hydra.langs.shex.syntax.NotStartAction value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NotStartAction)) {
        return false;
      }
      NotStartAction o = (NotStartAction) (other);
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