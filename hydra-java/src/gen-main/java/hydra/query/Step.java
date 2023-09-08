package hydra.query;

import java.io.Serializable;

/**
 * An atomic function as part of a query. When applied to a graph, steps are typed by function types.
 */
public abstract class Step implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/query.Step");
  
  private Step () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Edge instance) ;
    
    R visit(Project instance) ;
    
    R visit(Compare instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Step instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Edge instance) {
      return otherwise((instance));
    }
    
    default R visit(Project instance) {
      return otherwise((instance));
    }
    
    default R visit(Compare instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * An out-to-in traversal of an abstract edge
   */
  public static final class Edge extends hydra.query.Step implements Serializable {
    /**
     * An out-to-in traversal of an abstract edge
     */
    public final hydra.query.Edge value;
    
    public Edge (hydra.query.Edge value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Edge)) {
        return false;
      }
      Edge o = (Edge) (other);
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
   * A projection from a record through one of its fields
   */
  public static final class Project extends hydra.query.Step implements Serializable {
    /**
     * A projection from a record through one of its fields
     */
    public final hydra.core.Projection value;
    
    public Project (hydra.core.Projection value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Project)) {
        return false;
      }
      Project o = (Project) (other);
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
   * A comparison of two terms
   */
  public static final class Compare extends hydra.query.Step implements Serializable {
    /**
     * A comparison of two terms
     */
    public final hydra.query.ComparisonConstraint value;
    
    public Compare (hydra.query.ComparisonConstraint value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Compare)) {
        return false;
      }
      Compare o = (Compare) (other);
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