package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class RepeatRange_Sequence_Option_Option_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.RepeatRange.Sequence.Option.Option.Option");
  
  private RepeatRange_Sequence_Option_Option_Option () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Integer_ instance) ;
    
    R visit(Ast instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(RepeatRange_Sequence_Option_Option_Option instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Integer_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Ast instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Integer_ extends hydra.langs.shex.syntax.RepeatRange_Sequence_Option_Option_Option implements Serializable {
    public final hydra.langs.shex.syntax.Integer_ value;
    
    public Integer_ (hydra.langs.shex.syntax.Integer_ value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Integer_)) {
        return false;
      }
      Integer_ o = (Integer_) (other);
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
  
  public static final class Ast extends hydra.langs.shex.syntax.RepeatRange_Sequence_Option_Option_Option implements Serializable {
    public Ast () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Ast)) {
        return false;
      }
      Ast o = (Ast) (other);
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