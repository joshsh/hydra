// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Exact_Cardinality
 */
public class ObjectExactCardinality implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectExactCardinality");
  
  public final java.math.BigInteger bound;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public final java.util.List<hydra.langs.owl.syntax.ClassExpression> class_;
  
  public ObjectExactCardinality (java.math.BigInteger bound, hydra.langs.owl.syntax.ObjectPropertyExpression property, java.util.List<hydra.langs.owl.syntax.ClassExpression> class_) {
    if (bound == null) {
      throw new IllegalArgumentException("null value for 'bound' argument");
    }
    if (property == null) {
      throw new IllegalArgumentException("null value for 'property' argument");
    }
    if (class_ == null) {
      throw new IllegalArgumentException("null value for 'class' argument");
    }
    this.bound = bound;
    this.property = property;
    this.class_ = class_;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectExactCardinality)) {
      return false;
    }
    ObjectExactCardinality o = (ObjectExactCardinality) (other);
    return bound.equals(o.bound) && property.equals(o.property) && class_.equals(o.class_);
  }
  
  @Override
  public int hashCode() {
    return 2 * bound.hashCode() + 3 * property.hashCode() + 5 * class_.hashCode();
  }
  
  public ObjectExactCardinality withBound(java.math.BigInteger bound) {
    if (bound == null) {
      throw new IllegalArgumentException("null value for 'bound' argument");
    }
    return new ObjectExactCardinality(bound, property, class_);
  }
  
  public ObjectExactCardinality withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    if (property == null) {
      throw new IllegalArgumentException("null value for 'property' argument");
    }
    return new ObjectExactCardinality(bound, property, class_);
  }
  
  public ObjectExactCardinality withClass(java.util.List<hydra.langs.owl.syntax.ClassExpression> class_) {
    if (class_ == null) {
      throw new IllegalArgumentException("null value for 'class' argument");
    }
    return new ObjectExactCardinality(bound, property, class_);
  }
}