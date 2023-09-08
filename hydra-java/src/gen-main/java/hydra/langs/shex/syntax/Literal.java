package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class Literal implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Literal");
  
  private Literal () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(RdfLiteral instance) ;
    
    R visit(NumericLiteral instance) ;
    
    R visit(BooleanLiteral instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Literal instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(RdfLiteral instance) {
      return otherwise((instance));
    }
    
    default R visit(NumericLiteral instance) {
      return otherwise((instance));
    }
    
    default R visit(BooleanLiteral instance) {
      return otherwise((instance));
    }
  }
  
  public static final class RdfLiteral extends hydra.langs.shex.syntax.Literal implements Serializable {
    public final hydra.langs.shex.syntax.RdfLiteral value;
    
    public RdfLiteral (hydra.langs.shex.syntax.RdfLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof RdfLiteral)) {
        return false;
      }
      RdfLiteral o = (RdfLiteral) (other);
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
  
  public static final class NumericLiteral extends hydra.langs.shex.syntax.Literal implements Serializable {
    public final hydra.langs.shex.syntax.NumericLiteral value;
    
    public NumericLiteral (hydra.langs.shex.syntax.NumericLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NumericLiteral)) {
        return false;
      }
      NumericLiteral o = (NumericLiteral) (other);
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
  
  public static final class BooleanLiteral extends hydra.langs.shex.syntax.Literal implements Serializable {
    public final hydra.langs.shex.syntax.BooleanLiteral value;
    
    public BooleanLiteral (hydra.langs.shex.syntax.BooleanLiteral value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof BooleanLiteral)) {
        return false;
      }
      BooleanLiteral o = (BooleanLiteral) (other);
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