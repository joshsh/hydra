package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * Either a vertex or an edge
 */
public abstract class Element<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.Element");
  
  private Element () {
  
  }
  
  public abstract <R> R accept(Visitor<V, R> visitor) ;
  
  public interface Visitor<V, R> {
    R visit(Vertex<V> instance) ;
    
    R visit(Edge<V> instance) ;
  }
  
  public interface PartialVisitor<V, R> extends Visitor<V, R> {
    default R otherwise(Element<V> instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Vertex<V> instance) {
      return otherwise((instance));
    }
    
    default R visit(Edge<V> instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Vertex<V> extends hydra.langs.tinkerpop.propertyGraph.Element<V> implements Serializable {
    public final hydra.langs.tinkerpop.propertyGraph.Vertex<V> value;
    
    public Vertex (hydra.langs.tinkerpop.propertyGraph.Vertex<V> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Vertex)) {
        return false;
      }
      Vertex o = (Vertex) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<V, R> visitor) {
      return visitor.visit(this);
    }
  }
  
  public static final class Edge<V> extends hydra.langs.tinkerpop.propertyGraph.Element<V> implements Serializable {
    public final hydra.langs.tinkerpop.propertyGraph.Edge<V> value;
    
    public Edge (hydra.langs.tinkerpop.propertyGraph.Edge<V> value) {
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
    public <R> R accept(Visitor<V, R> visitor) {
      return visitor.visit(this);
    }
  }
}