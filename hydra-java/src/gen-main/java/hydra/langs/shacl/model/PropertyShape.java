package hydra.langs.shacl.model;

import java.io.Serializable;

/**
 * A SHACL property shape. See https://www.w3.org/TR/shacl/#property-shapes
 */
public class PropertyShape implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shacl/model.PropertyShape");
  
  public final hydra.langs.shacl.model.CommonProperties common;
  
  /**
   * Any property shape -specific constraint parameters
   */
  public final java.util.Set<hydra.langs.shacl.model.PropertyShapeConstraint> constraints;
  
  /**
   * See https://www.w3.org/TR/shacl/#defaultValue
   */
  public final java.util.Optional<hydra.langs.rdf.syntax.Node> defaultValue;
  
  /**
   * See https://www.w3.org/TR/shacl/#name
   */
  public final hydra.langs.rdf.syntax.LangStrings description;
  
  /**
   * See https://www.w3.org/TR/shacl/#name
   */
  public final hydra.langs.rdf.syntax.LangStrings name;
  
  /**
   * See https://www.w3.org/TR/shacl/#order
   */
  public final java.util.Optional<java.math.BigInteger> order;
  
  public final hydra.langs.rdf.syntax.Iri path;
  
  public PropertyShape (hydra.langs.shacl.model.CommonProperties common, java.util.Set<hydra.langs.shacl.model.PropertyShapeConstraint> constraints, java.util.Optional<hydra.langs.rdf.syntax.Node> defaultValue, hydra.langs.rdf.syntax.LangStrings description, hydra.langs.rdf.syntax.LangStrings name, java.util.Optional<java.math.BigInteger> order, hydra.langs.rdf.syntax.Iri path) {
    this.common = common;
    this.constraints = constraints;
    this.defaultValue = defaultValue;
    this.description = description;
    this.name = name;
    this.order = order;
    this.path = path;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PropertyShape)) {
      return false;
    }
    PropertyShape o = (PropertyShape) (other);
    return common.equals(o.common) && constraints.equals(o.constraints) && defaultValue.equals(o.defaultValue) && description.equals(o.description) && name.equals(o.name) && order.equals(o.order) && path.equals(o.path);
  }
  
  @Override
  public int hashCode() {
    return 2 * common.hashCode() + 3 * constraints.hashCode() + 5 * defaultValue.hashCode() + 7 * description.hashCode() + 11 * name.hashCode() + 13 * order.hashCode() + 17 * path.hashCode();
  }
  
  public PropertyShape withCommon(hydra.langs.shacl.model.CommonProperties common) {
    return new PropertyShape(common, constraints, defaultValue, description, name, order, path);
  }
  
  public PropertyShape withConstraints(java.util.Set<hydra.langs.shacl.model.PropertyShapeConstraint> constraints) {
    return new PropertyShape(common, constraints, defaultValue, description, name, order, path);
  }
  
  public PropertyShape withDefaultValue(java.util.Optional<hydra.langs.rdf.syntax.Node> defaultValue) {
    return new PropertyShape(common, constraints, defaultValue, description, name, order, path);
  }
  
  public PropertyShape withDescription(hydra.langs.rdf.syntax.LangStrings description) {
    return new PropertyShape(common, constraints, defaultValue, description, name, order, path);
  }
  
  public PropertyShape withName(hydra.langs.rdf.syntax.LangStrings name) {
    return new PropertyShape(common, constraints, defaultValue, description, name, order, path);
  }
  
  public PropertyShape withOrder(java.util.Optional<java.math.BigInteger> order) {
    return new PropertyShape(common, constraints, defaultValue, description, name, order, path);
  }
  
  public PropertyShape withPath(hydra.langs.rdf.syntax.Iri path) {
    return new PropertyShape(common, constraints, defaultValue, description, name, order, path);
  }
}