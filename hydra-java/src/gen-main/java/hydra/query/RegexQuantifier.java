package hydra.query;

import java.io.Serializable;

/**
 * A regular expression quantifier
 */
public abstract class RegexQuantifier implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/query.RegexQuantifier");
  
  private RegexQuantifier () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(One instance) ;
    
    R visit(ZeroOrOne instance) ;
    
    R visit(ZeroOrMore instance) ;
    
    R visit(OneOrMore instance) ;
    
    R visit(Exactly instance) ;
    
    R visit(AtLeast instance) ;
    
    R visit(Range instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(RegexQuantifier instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(One instance) {
      return otherwise((instance));
    }
    
    default R visit(ZeroOrOne instance) {
      return otherwise((instance));
    }
    
    default R visit(ZeroOrMore instance) {
      return otherwise((instance));
    }
    
    default R visit(OneOrMore instance) {
      return otherwise((instance));
    }
    
    default R visit(Exactly instance) {
      return otherwise((instance));
    }
    
    default R visit(AtLeast instance) {
      return otherwise((instance));
    }
    
    default R visit(Range instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * No quantifier; matches a single occurrence
   */
  public static final class One extends hydra.query.RegexQuantifier implements Serializable {
    public One () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof One)) {
        return false;
      }
      One o = (One) (other);
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
  
  /**
   * The ? quanifier; matches zero or one occurrence
   */
  public static final class ZeroOrOne extends hydra.query.RegexQuantifier implements Serializable {
    public ZeroOrOne () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ZeroOrOne)) {
        return false;
      }
      ZeroOrOne o = (ZeroOrOne) (other);
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
  
  /**
   * The * quantifier; matches any number of occurrences
   */
  public static final class ZeroOrMore extends hydra.query.RegexQuantifier implements Serializable {
    public ZeroOrMore () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ZeroOrMore)) {
        return false;
      }
      ZeroOrMore o = (ZeroOrMore) (other);
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
  
  /**
   * The + quantifier; matches one or more occurrences
   */
  public static final class OneOrMore extends hydra.query.RegexQuantifier implements Serializable {
    public OneOrMore () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof OneOrMore)) {
        return false;
      }
      OneOrMore o = (OneOrMore) (other);
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
  
  /**
   * The {n} quantifier; matches exactly n occurrences
   */
  public static final class Exactly extends hydra.query.RegexQuantifier implements Serializable {
    /**
     * The {n} quantifier; matches exactly n occurrences
     */
    public final Integer value;
    
    public Exactly (Integer value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Exactly)) {
        return false;
      }
      Exactly o = (Exactly) (other);
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
  
  /**
   * The {n,} quantifier; matches at least n occurrences
   */
  public static final class AtLeast extends hydra.query.RegexQuantifier implements Serializable {
    /**
     * The {n,} quantifier; matches at least n occurrences
     */
    public final Integer value;
    
    public AtLeast (Integer value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof AtLeast)) {
        return false;
      }
      AtLeast o = (AtLeast) (other);
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
  
  /**
   * The {n, m} quantifier; matches between n and m (inclusive) occurrences
   */
  public static final class Range extends hydra.query.RegexQuantifier implements Serializable {
    /**
     * The {n, m} quantifier; matches between n and m (inclusive) occurrences
     */
    public final hydra.query.Range value;
    
    public Range (hydra.query.Range value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Range)) {
        return false;
      }
      Range o = (Range) (other);
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