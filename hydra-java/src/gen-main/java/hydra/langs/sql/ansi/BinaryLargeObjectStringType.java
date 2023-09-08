package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class BinaryLargeObjectStringType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BinaryLargeObjectStringType");
  
  private BinaryLargeObjectStringType () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Binary instance) ;
    
    R visit(Blob instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(BinaryLargeObjectStringType instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Binary instance) {
      return otherwise((instance));
    }
    
    default R visit(Blob instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Binary extends hydra.langs.sql.ansi.BinaryLargeObjectStringType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value;
    
    public Binary (java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Binary)) {
        return false;
      }
      Binary o = (Binary) (other);
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
  
  public static final class Blob extends hydra.langs.sql.ansi.BinaryLargeObjectStringType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value;
    
    public Blob (java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Blob)) {
        return false;
      }
      Blob o = (Blob) (other);
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