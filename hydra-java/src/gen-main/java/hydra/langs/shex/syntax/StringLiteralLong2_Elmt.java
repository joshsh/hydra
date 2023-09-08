package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class StringLiteralLong2_Elmt implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringLiteralLong2.Elmt");
  
  private StringLiteralLong2_Elmt () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Sequence instance) ;
    
    R visit(Echar instance) ;
    
    R visit(Uchar instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(StringLiteralLong2_Elmt instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Sequence instance) {
      return otherwise((instance));
    }
    
    default R visit(Echar instance) {
      return otherwise((instance));
    }
    
    default R visit(Uchar instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Sequence extends hydra.langs.shex.syntax.StringLiteralLong2_Elmt implements Serializable {
    public final hydra.langs.shex.syntax.StringLiteralLong2_Elmt_Sequence value;
    
    public Sequence (hydra.langs.shex.syntax.StringLiteralLong2_Elmt_Sequence value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sequence)) {
        return false;
      }
      Sequence o = (Sequence) (other);
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
  
  public static final class Echar extends hydra.langs.shex.syntax.StringLiteralLong2_Elmt implements Serializable {
    public final hydra.langs.shex.syntax.Echar value;
    
    public Echar (hydra.langs.shex.syntax.Echar value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Echar)) {
        return false;
      }
      Echar o = (Echar) (other);
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
  
  public static final class Uchar extends hydra.langs.shex.syntax.StringLiteralLong2_Elmt implements Serializable {
    public final hydra.langs.shex.syntax.Uchar value;
    
    public Uchar (hydra.langs.shex.syntax.Uchar value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Uchar)) {
        return false;
      }
      Uchar o = (Uchar) (other);
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