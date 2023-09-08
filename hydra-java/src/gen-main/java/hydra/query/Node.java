package hydra.query;

import java.io.Serializable;

/**
 * A node in a query expression; it may be a term, a variable, or a wildcard
 */
public abstract class Node<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/query.Node");
  
  private Node () {
  
  }
  
  public abstract <R> R accept(Visitor<A, R> visitor) ;
  
  public interface Visitor<A, R> {
    R visit(Term<A> instance) ;
    
    R visit(Variable<A> instance) ;
    
    R visit(Wildcard<A> instance) ;
  }
  
  public interface PartialVisitor<A, R> extends Visitor<A, R> {
    default R otherwise(Node<A> instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Term<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Variable<A> instance) {
      return otherwise((instance));
    }
    
    default R visit(Wildcard<A> instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * A graph term; an expression which is valid in the graph being matched
   */
  public static final class Term<A> extends hydra.query.Node<A> implements Serializable {
    /**
     * A graph term; an expression which is valid in the graph being matched
     */
    public final hydra.core.Term<A> value;
    
    public Term (hydra.core.Term<A> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Term)) {
        return false;
      }
      Term o = (Term) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<A, R> visitor) {
      return visitor.visit(this);
    }
  }
  
  /**
   * A query variable, not to be confused with a variable term
   */
  public static final class Variable<A> extends hydra.query.Node<A> implements Serializable {
    /**
     * A query variable, not to be confused with a variable term
     */
    public final hydra.query.Variable value;
    
    public Variable (hydra.query.Variable value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Variable)) {
        return false;
      }
      Variable o = (Variable) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<A, R> visitor) {
      return visitor.visit(this);
    }
  }
  
  /**
   * An anonymous variable which we do not care to join across patterns
   */
  public static final class Wildcard<A> extends hydra.query.Node<A> implements Serializable {
    public Wildcard () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Wildcard)) {
        return false;
      }
      Wildcard o = (Wildcard) (other);
      return true;
    }
    
    @Override
    public int hashCode() {
      return 0;
    }
    
    @Override
    public <R> R accept(Visitor<A, R> visitor) {
      return visitor.visit(this);
    }
  }
}