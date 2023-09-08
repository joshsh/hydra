package hydra.grammar;

import java.io.Serializable;

/**
 * A pattern which matches valid expressions in the language
 */
public abstract class Pattern implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/grammar.Pattern");
  
  private Pattern () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Nil instance) ;
    
    R visit(Ignored instance) ;
    
    R visit(Labeled instance) ;
    
    R visit(Constant instance) ;
    
    R visit(Regex instance) ;
    
    R visit(Nonterminal instance) ;
    
    R visit(Sequence instance) ;
    
    R visit(Alternatives instance) ;
    
    R visit(Option instance) ;
    
    R visit(Star instance) ;
    
    R visit(Plus instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Pattern instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Nil instance) {
      return otherwise((instance));
    }
    
    default R visit(Ignored instance) {
      return otherwise((instance));
    }
    
    default R visit(Labeled instance) {
      return otherwise((instance));
    }
    
    default R visit(Constant instance) {
      return otherwise((instance));
    }
    
    default R visit(Regex instance) {
      return otherwise((instance));
    }
    
    default R visit(Nonterminal instance) {
      return otherwise((instance));
    }
    
    default R visit(Sequence instance) {
      return otherwise((instance));
    }
    
    default R visit(Alternatives instance) {
      return otherwise((instance));
    }
    
    default R visit(Option instance) {
      return otherwise((instance));
    }
    
    default R visit(Star instance) {
      return otherwise((instance));
    }
    
    default R visit(Plus instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Nil extends hydra.grammar.Pattern implements Serializable {
    public Nil () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Nil)) {
        return false;
      }
      Nil o = (Nil) (other);
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
  
  public static final class Ignored extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.Pattern value;
    
    public Ignored (hydra.grammar.Pattern value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Ignored)) {
        return false;
      }
      Ignored o = (Ignored) (other);
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
  
  public static final class Labeled extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.LabeledPattern value;
    
    public Labeled (hydra.grammar.LabeledPattern value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Labeled)) {
        return false;
      }
      Labeled o = (Labeled) (other);
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
  
  public static final class Constant extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.Constant value;
    
    public Constant (hydra.grammar.Constant value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Constant)) {
        return false;
      }
      Constant o = (Constant) (other);
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
  
  public static final class Regex extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.Regex value;
    
    public Regex (hydra.grammar.Regex value) {
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
  
  public static final class Nonterminal extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.Symbol value;
    
    public Nonterminal (hydra.grammar.Symbol value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Nonterminal)) {
        return false;
      }
      Nonterminal o = (Nonterminal) (other);
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
  
  public static final class Sequence extends hydra.grammar.Pattern implements Serializable {
    public final java.util.List<hydra.grammar.Pattern> value;
    
    public Sequence (java.util.List<hydra.grammar.Pattern> value) {
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
  
  public static final class Alternatives extends hydra.grammar.Pattern implements Serializable {
    public final java.util.List<hydra.grammar.Pattern> value;
    
    public Alternatives (java.util.List<hydra.grammar.Pattern> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Alternatives)) {
        return false;
      }
      Alternatives o = (Alternatives) (other);
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
  
  public static final class Option extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.Pattern value;
    
    public Option (hydra.grammar.Pattern value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Option)) {
        return false;
      }
      Option o = (Option) (other);
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
  
  public static final class Star extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.Pattern value;
    
    public Star (hydra.grammar.Pattern value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Star)) {
        return false;
      }
      Star o = (Star) (other);
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
  
  public static final class Plus extends hydra.grammar.Pattern implements Serializable {
    public final hydra.grammar.Pattern value;
    
    public Plus (hydra.grammar.Pattern value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Plus)) {
        return false;
      }
      Plus o = (Plus) (other);
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