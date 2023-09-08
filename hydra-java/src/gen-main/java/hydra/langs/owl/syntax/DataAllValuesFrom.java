package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DataAllValuesFrom implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataAllValuesFrom");
  
  public final java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> property;
  
  public final hydra.langs.owl.syntax.DataRange range;
  
  public DataAllValuesFrom (java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> property, hydra.langs.owl.syntax.DataRange range) {
    this.property = property;
    this.range = range;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataAllValuesFrom)) {
      return false;
    }
    DataAllValuesFrom o = (DataAllValuesFrom) (other);
    return property.equals(o.property) && range.equals(o.range);
  }
  
  @Override
  public int hashCode() {
    return 2 * property.hashCode() + 3 * range.hashCode();
  }
  
  public DataAllValuesFrom withProperty(java.util.List<hydra.langs.owl.syntax.DataPropertyExpression> property) {
    return new DataAllValuesFrom(property, range);
  }
  
  public DataAllValuesFrom withRange(hydra.langs.owl.syntax.DataRange range) {
    return new DataAllValuesFrom(property, range);
  }
}