// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.gremlin;

import java.io.Serializable;

public abstract class TraversalPredicate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/gremlin.TraversalPredicate");
  
  private TraversalPredicate () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Eq instance) ;
    
    R visit(Neq instance) ;
    
    R visit(Lt instance) ;
    
    R visit(Lte instance) ;
    
    R visit(Gt instance) ;
    
    R visit(Gte instance) ;
    
    R visit(Inside instance) ;
    
    R visit(Outside instance) ;
    
    R visit(Between instance) ;
    
    R visit(Within instance) ;
    
    R visit(Without instance) ;
    
    R visit(Not instance) ;
    
    R visit(StartingWith instance) ;
    
    R visit(NotStartingWith instance) ;
    
    R visit(EndingWith instance) ;
    
    R visit(NotEndingWith instance) ;
    
    R visit(Containing instance) ;
    
    R visit(NotContaining instance) ;
    
    R visit(Regex instance) ;
    
    R visit(NotRegex instance) ;
    
    R visit(And instance) ;
    
    R visit(Or instance) ;
    
    R visit(Negate instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TraversalPredicate instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Eq instance) {
      return otherwise((instance));
    }
    
    default R visit(Neq instance) {
      return otherwise((instance));
    }
    
    default R visit(Lt instance) {
      return otherwise((instance));
    }
    
    default R visit(Lte instance) {
      return otherwise((instance));
    }
    
    default R visit(Gt instance) {
      return otherwise((instance));
    }
    
    default R visit(Gte instance) {
      return otherwise((instance));
    }
    
    default R visit(Inside instance) {
      return otherwise((instance));
    }
    
    default R visit(Outside instance) {
      return otherwise((instance));
    }
    
    default R visit(Between instance) {
      return otherwise((instance));
    }
    
    default R visit(Within instance) {
      return otherwise((instance));
    }
    
    default R visit(Without instance) {
      return otherwise((instance));
    }
    
    default R visit(Not instance) {
      return otherwise((instance));
    }
    
    default R visit(StartingWith instance) {
      return otherwise((instance));
    }
    
    default R visit(NotStartingWith instance) {
      return otherwise((instance));
    }
    
    default R visit(EndingWith instance) {
      return otherwise((instance));
    }
    
    default R visit(NotEndingWith instance) {
      return otherwise((instance));
    }
    
    default R visit(Containing instance) {
      return otherwise((instance));
    }
    
    default R visit(NotContaining instance) {
      return otherwise((instance));
    }
    
    default R visit(Regex instance) {
      return otherwise((instance));
    }
    
    default R visit(NotRegex instance) {
      return otherwise((instance));
    }
    
    default R visit(And instance) {
      return otherwise((instance));
    }
    
    default R visit(Or instance) {
      return otherwise((instance));
    }
    
    default R visit(Negate instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Eq extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value;
    
    public Eq (hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Eq)) {
        return false;
      }
      Eq o = (Eq) (other);
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
  
  public static final class Neq extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value;
    
    public Neq (hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Neq)) {
        return false;
      }
      Neq o = (Neq) (other);
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
  
  public static final class Lt extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value;
    
    public Lt (hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Lt)) {
        return false;
      }
      Lt o = (Lt) (other);
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
  
  public static final class Lte extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value;
    
    public Lte (hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Lte)) {
        return false;
      }
      Lte o = (Lte) (other);
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
  
  public static final class Gt extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value;
    
    public Gt (hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Gt)) {
        return false;
      }
      Gt o = (Gt) (other);
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
  
  public static final class Gte extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value;
    
    public Gte (hydra.langs.tinkerpop.gremlin.GenericLiteralArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Gte)) {
        return false;
      }
      Gte o = (Gte) (other);
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
  
  public static final class Inside extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.RangeArgument value;
    
    public Inside (hydra.langs.tinkerpop.gremlin.RangeArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Inside)) {
        return false;
      }
      Inside o = (Inside) (other);
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
  
  public static final class Outside extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.RangeArgument value;
    
    public Outside (hydra.langs.tinkerpop.gremlin.RangeArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Outside)) {
        return false;
      }
      Outside o = (Outside) (other);
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
  
  public static final class Between extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.RangeArgument value;
    
    public Between (hydra.langs.tinkerpop.gremlin.RangeArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Between)) {
        return false;
      }
      Between o = (Between) (other);
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
  
  public static final class Within extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final java.util.Optional<hydra.langs.tinkerpop.gremlin.GenericLiteralArgument> value;
    
    public Within (java.util.Optional<hydra.langs.tinkerpop.gremlin.GenericLiteralArgument> value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Within)) {
        return false;
      }
      Within o = (Within) (other);
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
  
  public static final class Without extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final java.util.Optional<hydra.langs.tinkerpop.gremlin.GenericLiteralArgument> value;
    
    public Without (java.util.Optional<hydra.langs.tinkerpop.gremlin.GenericLiteralArgument> value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Without)) {
        return false;
      }
      Without o = (Without) (other);
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
  
  public static final class Not extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.TraversalPredicate value;
    
    public Not (hydra.langs.tinkerpop.gremlin.TraversalPredicate value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Not)) {
        return false;
      }
      Not o = (Not) (other);
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
  
  public static final class StartingWith extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public StartingWith (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof StartingWith)) {
        return false;
      }
      StartingWith o = (StartingWith) (other);
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
  
  public static final class NotStartingWith extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public NotStartingWith (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NotStartingWith)) {
        return false;
      }
      NotStartingWith o = (NotStartingWith) (other);
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
  
  public static final class EndingWith extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public EndingWith (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof EndingWith)) {
        return false;
      }
      EndingWith o = (EndingWith) (other);
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
  
  public static final class NotEndingWith extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public NotEndingWith (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NotEndingWith)) {
        return false;
      }
      NotEndingWith o = (NotEndingWith) (other);
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
  
  public static final class Containing extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public Containing (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Containing)) {
        return false;
      }
      Containing o = (Containing) (other);
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
  
  public static final class NotContaining extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public NotContaining (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NotContaining)) {
        return false;
      }
      NotContaining o = (NotContaining) (other);
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
  
  public static final class Regex extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public Regex (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
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
  
  public static final class NotRegex extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.StringArgument value;
    
    public NotRegex (hydra.langs.tinkerpop.gremlin.StringArgument value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NotRegex)) {
        return false;
      }
      NotRegex o = (NotRegex) (other);
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
  
  public static final class And extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.TwoTraversalPredicates value;
    
    public And (hydra.langs.tinkerpop.gremlin.TwoTraversalPredicates value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof And)) {
        return false;
      }
      And o = (And) (other);
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
  
  public static final class Or extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.TwoTraversalPredicates value;
    
    public Or (hydra.langs.tinkerpop.gremlin.TwoTraversalPredicates value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Or)) {
        return false;
      }
      Or o = (Or) (other);
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
  
  public static final class Negate extends hydra.langs.tinkerpop.gremlin.TraversalPredicate implements Serializable {
    public final hydra.langs.tinkerpop.gremlin.TraversalPredicate value;
    
    public Negate (hydra.langs.tinkerpop.gremlin.TraversalPredicate value) {
      if (value == null) {
        throw new IllegalArgumentException("null value for 'value' argument");
      }
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Negate)) {
        return false;
      }
      Negate o = (Negate) (other);
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