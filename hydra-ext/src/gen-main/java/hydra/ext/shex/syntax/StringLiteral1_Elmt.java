// Note: this is an automatically generated file. Do not edit.

package hydra.ext.shex.syntax;

import java.io.Serializable;

public abstract class StringLiteral1_Elmt implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/ext/shex/syntax.StringLiteral1.Elmt");
  
  public static final hydra.core.Name FIELD_NAME_REGEX = new hydra.core.Name("regex");
  
  public static final hydra.core.Name FIELD_NAME_ECHAR = new hydra.core.Name("echar");
  
  public static final hydra.core.Name FIELD_NAME_UCHAR = new hydra.core.Name("uchar");
  
  private StringLiteral1_Elmt () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Regex instance) ;
    
    R visit(Echar instance) ;
    
    R visit(Uchar instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(StringLiteral1_Elmt instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Regex instance) {
      return otherwise((instance));
    }
    
    default R visit(Echar instance) {
      return otherwise((instance));
    }
    
    default R visit(Uchar instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Regex extends hydra.ext.shex.syntax.StringLiteral1_Elmt implements Serializable {
    public final String value;
    
    public Regex (String value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Regex)) {
        return false;
      }
      Regex o = (Regex) (other);
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
  
  public static final class Echar extends hydra.ext.shex.syntax.StringLiteral1_Elmt implements Serializable {
    public final hydra.ext.shex.syntax.Echar value;
    
    public Echar (hydra.ext.shex.syntax.Echar value) {
      java.util.Objects.requireNonNull((value));
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
  
  public static final class Uchar extends hydra.ext.shex.syntax.StringLiteral1_Elmt implements Serializable {
    public final hydra.ext.shex.syntax.Uchar value;
    
    public Uchar (hydra.ext.shex.syntax.Uchar value) {
      java.util.Objects.requireNonNull((value));
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