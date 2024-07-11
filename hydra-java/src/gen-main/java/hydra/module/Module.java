// Note: this is an automatically generated file. Do not edit.

package hydra.module;

import hydra.util.Opt;

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
   * Any modules which the term expressions of this module directly depend upon
   */
  public final java.util.List<hydra.module.Module<A>> termDependencies;
  
  /**
   * Any modules which the type expressions of this module directly depend upon
   */
  public final java.util.List<hydra.module.Module<A>> typeDependencies;
  
  /**
   * An optional human-readable description of the module
   */
  public final Opt<String> description;
  
  public Module (hydra.module.Namespace namespace, java.util.List<hydra.graph.Element<A>> elements, java.util.List<hydra.module.Module<A>> termDependencies, java.util.List<hydra.module.Module<A>> typeDependencies, Opt<String> description) {
    if (namespace == null) {
      throw new IllegalArgumentException("null value for 'namespace' argument");
    }
    if (elements == null) {
      throw new IllegalArgumentException("null value for 'elements' argument");
    }
    if (termDependencies == null) {
      throw new IllegalArgumentException("null value for 'termDependencies' argument");
    }
    if (typeDependencies == null) {
      throw new IllegalArgumentException("null value for 'typeDependencies' argument");
    }
    if (description == null) {
      throw new IllegalArgumentException("null value for 'description' argument");
    }
    this.namespace = namespace;
    this.elements = elements;
    this.termDependencies = termDependencies;
    this.typeDependencies = typeDependencies;
    this.description = description;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Module)) {
      return false;
    }
    Module o = (Module) (other);
    return namespace.equals(o.namespace) && elements.equals(o.elements) && termDependencies.equals(o.termDependencies) && typeDependencies.equals(o.typeDependencies) && description.equals(o.description);
  }
  
  @Override
  public int hashCode() {
    return 2 * namespace.hashCode() + 3 * elements.hashCode() + 5 * termDependencies.hashCode() + 7 * typeDependencies.hashCode() + 11 * description.hashCode();
  }
  
  public Module withNamespace(hydra.module.Namespace namespace) {
    if (namespace == null) {
      throw new IllegalArgumentException("null value for 'namespace' argument");
    }
    return new Module(namespace, elements, termDependencies, typeDependencies, description);
  }
  
  public Module withElements(java.util.List<hydra.graph.Element<A>> elements) {
    if (elements == null) {
      throw new IllegalArgumentException("null value for 'elements' argument");
    }
    return new Module(namespace, elements, termDependencies, typeDependencies, description);
  }
  
  public Module withTermDependencies(java.util.List<hydra.module.Module<A>> termDependencies) {
    if (termDependencies == null) {
      throw new IllegalArgumentException("null value for 'termDependencies' argument");
    }
    return new Module(namespace, elements, termDependencies, typeDependencies, description);
  }
  
  public Module withTypeDependencies(java.util.List<hydra.module.Module<A>> typeDependencies) {
    if (typeDependencies == null) {
      throw new IllegalArgumentException("null value for 'typeDependencies' argument");
    }
    return new Module(namespace, elements, termDependencies, typeDependencies, description);
  }
  
  public Module withDescription(Opt<String> description) {
    if (description == null) {
      throw new IllegalArgumentException("null value for 'description' argument");
    }
    return new Module(namespace, elements, termDependencies, typeDependencies, description);
  }
}
