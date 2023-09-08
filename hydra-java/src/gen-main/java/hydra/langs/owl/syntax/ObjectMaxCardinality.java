package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Maximum_Cardinality
 */
public class ObjectMaxCardinality implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectMaxCardinality");
  
  public final java.math.BigInteger bound;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public final java.util.List<hydra.langs.owl.syntax.ClassExpression> class_;
  
  public ObjectMaxCardinality (java.math.BigInteger bound, hydra.langs.owl.syntax.ObjectPropertyExpression property, java.util.List<hydra.langs.owl.syntax.ClassExpression> class_) {
    this.bound = bound;
    this.property = property;
    this.class_ = class_;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectMaxCardinality)) {
      return false;
    }
    ObjectMaxCardinality o = (ObjectMaxCardinality) (other);
    return bound.equals(o.bound) && property.equals(o.property) && class_.equals(o.class_);
  }
  
  @Override
  public int hashCode() {
    return 2 * bound.hashCode() + 3 * property.hashCode() + 5 * class_.hashCode();
  }
  
  public ObjectMaxCardinality withBound(java.math.BigInteger bound) {
    return new ObjectMaxCardinality(bound, property, class_);
  }
  
  public ObjectMaxCardinality withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    return new ObjectMaxCardinality(bound, property, class_);
  }
  
  public ObjectMaxCardinality withClass(java.util.List<hydra.langs.owl.syntax.ClassExpression> class_) {
    return new ObjectMaxCardinality(bound, property, class_);
  }
}