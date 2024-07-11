// Note: this is an automatically generated file. Do not edit.

package hydra.langs.cypher.openCypher;

import java.io.Serializable;

public abstract class StarOrYieldItems implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/cypher/openCypher.StarOrYieldItems");
  
  private StarOrYieldItems () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Star instance) ;
    
    R visit(Items instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(StarOrYieldItems instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Star instance) {
      return otherwise((instance));
    }
    
    default R visit(Items instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Star extends hydra.langs.cypher.openCypher.StarOrYieldItems implements Serializable {
    public Star () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Star)) {
        return false;
      }
      Star o = (Star) (other);
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
  
  public static final class Items extends hydra.langs.cypher.openCypher.StarOrYieldItems implements Serializable {
    public final hydra.langs.cypher.openCypher.YieldItems value;
    
    public Items (hydra.langs.cypher.openCypher.YieldItems value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Items)) {
        return false;
      }
      Items o = (Items) (other);
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