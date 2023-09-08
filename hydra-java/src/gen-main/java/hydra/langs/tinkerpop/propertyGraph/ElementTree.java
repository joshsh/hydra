package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * An element together with its dependencies in some context
 */
public class ElementTree<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.ElementTree");
  
  public final hydra.langs.tinkerpop.propertyGraph.Element<V> self;
  
  public final java.util.List<hydra.langs.tinkerpop.propertyGraph.ElementTree<V>> dependencies;
  
  public ElementTree (hydra.langs.tinkerpop.propertyGraph.Element<V> self, java.util.List<hydra.langs.tinkerpop.propertyGraph.ElementTree<V>> dependencies) {
    this.self = self;
    this.dependencies = dependencies;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ElementTree)) {
      return false;
    }
    ElementTree o = (ElementTree) (other);
    return self.equals(o.self) && dependencies.equals(o.dependencies);
  }
  
  @Override
  public int hashCode() {
    return 2 * self.hashCode() + 3 * dependencies.hashCode();
  }
  
  public ElementTree withSelf(hydra.langs.tinkerpop.propertyGraph.Element<V> self) {
    return new ElementTree(self, dependencies);
  }
  
  public ElementTree withDependencies(java.util.List<hydra.langs.tinkerpop.propertyGraph.ElementTree<V>> dependencies) {
    return new ElementTree(self, dependencies);
  }
}