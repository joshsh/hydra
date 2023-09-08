package hydra.langs.scala.meta;

import java.io.Serializable;

public abstract class Enumerator implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Enumerator");
  
  private Enumerator () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Generator instance) ;
    
    R visit(CaseGenerator instance) ;
    
    R visit(Val instance) ;
    
    R visit(Guard instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Enumerator instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Generator instance) {
      return otherwise((instance));
    }
    
    default R visit(CaseGenerator instance) {
      return otherwise((instance));
    }
    
    default R visit(Val instance) {
      return otherwise((instance));
    }
    
    default R visit(Guard instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Generator extends hydra.langs.scala.meta.Enumerator implements Serializable {
    public final hydra.langs.scala.meta.Enumerator_Generator value;
    
    public Generator (hydra.langs.scala.meta.Enumerator_Generator value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Generator)) {
        return false;
      }
      Generator o = (Generator) (other);
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
  
  public static final class CaseGenerator extends hydra.langs.scala.meta.Enumerator implements Serializable {
    public final hydra.langs.scala.meta.Enumerator_CaseGenerator value;
    
    public CaseGenerator (hydra.langs.scala.meta.Enumerator_CaseGenerator value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof CaseGenerator)) {
        return false;
      }
      CaseGenerator o = (CaseGenerator) (other);
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
  
  public static final class Val extends hydra.langs.scala.meta.Enumerator implements Serializable {
    public final hydra.langs.scala.meta.Enumerator_Val value;
    
    public Val (hydra.langs.scala.meta.Enumerator_Val value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Val)) {
        return false;
      }
      Val o = (Val) (other);
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
  
  public static final class Guard extends hydra.langs.scala.meta.Enumerator implements Serializable {
    public final hydra.langs.scala.meta.Enumerator_Guard value;
    
    public Guard (hydra.langs.scala.meta.Enumerator_Guard value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Guard)) {
        return false;
      }
      Guard o = (Guard) (other);
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