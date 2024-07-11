// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DataHasValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataHasValue");
  
  public final hydra.langs.owl.syntax.DataPropertyExpression property;
  
  public final hydra.langs.rdf.syntax.Literal value;
  
  public DataHasValue (hydra.langs.owl.syntax.DataPropertyExpression property, hydra.langs.rdf.syntax.Literal value) {
    java.util.Objects.requireNonNull((property));
    java.util.Objects.requireNonNull((value));
    this.property = property;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataHasValue)) {
      return false;
    }
    DataHasValue o = (DataHasValue) (other);
    return property.equals(o.property) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * property.hashCode() + 3 * value.hashCode();
  }
  
  public DataHasValue withProperty(hydra.langs.owl.syntax.DataPropertyExpression property) {
    java.util.Objects.requireNonNull((property));
    return new DataHasValue(property, value);
  }
  
  public DataHasValue withValue(hydra.langs.rdf.syntax.Literal value) {
    java.util.Objects.requireNonNull((value));
    return new DataHasValue(property, value);
  }
}