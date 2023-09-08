package hydra.module;

import java.io.Serializable;

/**
 * A logical collection of elements in the same namespace, having dependencies on zero or more other modules
 */
public class Module<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/module.Module");
  
  /**
   * A common prefix for all element names in the module
   */
  public final hydra.module.Namespace namespace;
  
  /**
   * The elements defined in this module
   */
  public final java.util.List<hydra.graph.Element<A>> elements;
  
  /**
   * Any additional modules this one has a direct dependency upon
   */
  public final java.util.List<hydra.module.Module<A>> dependencies;
  
  /**
   * An optional human-readable description of the module
   */
  public final java.util.Optional<String> description;
  
  public Module (hydra.module.Namespace namespace, java.util.List<hydra.graph.Element<A>> elements, java.util.List<hydra.module.Module<A>> dependencies, java.util.Optional<String> description) {
    this.namespace = namespace;
    this.elements = elements;
    this.dependencies = dependencies;
    this.description = description;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Module)) {
      return false;
    }
    Module o = (Module) (other);
    return namespace.equals(o.namespace) && elements.equals(o.elements) && dependencies.equals(o.dependencies) && description.equals(o.description);
  }
  
  @Override
  public int hashCode() {
    return 2 * namespace.hashCode() + 3 * elements.hashCode() + 5 * dependencies.hashCode() + 7 * description.hashCode();
  }
  
  public Module withNamespace(hydra.module.Namespace namespace) {
    return new Module(namespace, elements, dependencies, description);
  }
  
  public Module withElements(java.util.List<hydra.graph.Element<A>> elements) {
    return new Module(namespace, elements, dependencies, description);
  }
  
  public Module withDependencies(java.util.List<hydra.module.Module<A>> dependencies) {
    return new Module(namespace, elements, dependencies, description);
  }
  
  public Module withDescription(java.util.Optional<String> description) {
    return new Module(namespace, elements, dependencies, description);
  }
}