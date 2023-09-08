package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * An element type together with its dependencies in some context
 */
public class ElementTypeTree<T> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.ElementTypeTree");
  
  public final hydra.langs.tinkerpop.propertyGraph.ElementType<T> self;
  
  public final java.util.List<hydra.langs.tinkerpop.propertyGraph.ElementTypeTree<T>> dependencies;
  
  public ElementTypeTree (hydra.langs.tinkerpop.propertyGraph.ElementType<T> self, java.util.List<hydra.langs.tinkerpop.propertyGraph.ElementTypeTree<T>> dependencies) {
    this.self = self;
    this.dependencies = dependencies;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ElementTypeTree)) {
      return false;
    }
    ElementTypeTree o = (ElementTypeTree) (other);
    return self.equals(o.self) && dependencies.equals(o.dependencies);
  }
  
  @Override
  public int hashCode() {
    return 2 * self.hashCode() + 3 * dependencies.hashCode();
  }
  
  public ElementTypeTree withSelf(hydra.langs.tinkerpop.propertyGraph.ElementType<T> self) {
    return new ElementTypeTree(self, dependencies);
  }
  
  public ElementTypeTree withDependencies(java.util.List<hydra.langs.tinkerpop.propertyGraph.ElementTypeTree<T>> dependencies) {
    return new ElementTypeTree(self, dependencies);
  }
}