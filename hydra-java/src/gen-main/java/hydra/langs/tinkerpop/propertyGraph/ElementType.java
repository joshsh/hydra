package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * The type of a vertex or edge
 */
public abstract class ElementType<T> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.ElementType");
  
  private ElementType () {
  
  }
  
  public abstract <R> R accept(Visitor<T, R> visitor) ;
  
  public interface Visitor<T, R> {
    R visit(Vertex<T> instance) ;
    
    R visit(Edge<T> instance) ;
  }
  
  public interface PartialVisitor<T, R> extends Visitor<T, R> {
    default R otherwise(ElementType<T> instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Vertex<T> instance) {
      return otherwise((instance));
    }
    
    default R visit(Edge<T> instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Vertex<T> extends hydra.langs.tinkerpop.propertyGraph.ElementType<T> implements Serializable {
    public final hydra.langs.tinkerpop.propertyGraph.VertexType<T> value;
    
    public Vertex (hydra.langs.tinkerpop.propertyGraph.VertexType<T> value) {
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
    public <R> R accept(Visitor<T, R> visitor) {
      return visitor.visit(this);
    }
  }
  
  public static final class Edge<T> extends hydra.langs.tinkerpop.propertyGraph.ElementType<T> implements Serializable {
    public final hydra.langs.tinkerpop.propertyGraph.EdgeType<T> value;
    
    public Edge (hydra.langs.tinkerpop.propertyGraph.EdgeType<T> value) {
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
    public <R> R accept(Visitor<T, R> visitor) {
      return visitor.visit(this);
    }
  }
}