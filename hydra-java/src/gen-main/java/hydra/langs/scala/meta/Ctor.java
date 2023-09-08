package hydra.langs.scala.meta;

import java.io.Serializable;

public abstract class Ctor implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Ctor");
  
  private Ctor () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Primary instance) ;
    
    R visit(Secondary instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Ctor instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Primary instance) {
      return otherwise((instance));
    }
    
    default R visit(Secondary instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Primary extends hydra.langs.scala.meta.Ctor implements Serializable {
    public final hydra.langs.scala.meta.Ctor_Primary value;
    
    public Primary (hydra.langs.scala.meta.Ctor_Primary value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Primary)) {
        return false;
      }
      Primary o = (Primary) (other);
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
  
  public static final class Secondary extends hydra.langs.scala.meta.Ctor implements Serializable {
    public final hydra.langs.scala.meta.Ctor_Secondary value;
    
    public Secondary (hydra.langs.scala.meta.Ctor_Secondary value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Secondary)) {
        return false;
      }
      Secondary o = (Secondary) (other);
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