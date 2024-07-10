// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class ObjectHasValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectHasValue");
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public final hydra.langs.owl.syntax.Individual individual;
  
  public ObjectHasValue (hydra.langs.owl.syntax.ObjectPropertyExpression property, hydra.langs.owl.syntax.Individual individual) {
    if (property == null) {
      throw new IllegalArgumentException("null value for 'property' argument");
    }
    if (individual == null) {
      throw new IllegalArgumentException("null value for 'individual' argument");
    }
    this.property = property;
    this.individual = individual;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectHasValue)) {
      return false;
    }
    ObjectHasValue o = (ObjectHasValue) (other);
    return property.equals(o.property) && individual.equals(o.individual);
  }
  
  @Override
  public int hashCode() {
    return 2 * property.hashCode() + 3 * individual.hashCode();
  }
  
  public ObjectHasValue withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    if (property == null) {
      throw new IllegalArgumentException("null value for 'property' argument");
    }
    return new ObjectHasValue(property, individual);
  }
  
  public ObjectHasValue withIndividual(hydra.langs.owl.syntax.Individual individual) {
    if (individual == null) {
      throw new IllegalArgumentException("null value for 'individual' argument");
    }
    return new ObjectHasValue(property, individual);
  }
}