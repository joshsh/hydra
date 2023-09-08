package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DataMinCardinality implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataMinCardinality");
  
  public final java.math.BigInteger bound;
  
  public final hydra.langs.owl.syntax.DataPropertyExpression property;
  
  public final java.util.List<hydra.langs.owl.syntax.DataRange> range;
  
  public DataMinCardinality (java.math.BigInteger bound, hydra.langs.owl.syntax.DataPropertyExpression property, java.util.List<hydra.langs.owl.syntax.DataRange> range) {
    this.bound = bound;
    this.property = property;
    this.range = range;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataMinCardinality)) {
      return false;
    }
    DataMinCardinality o = (DataMinCardinality) (other);
    return bound.equals(o.bound) && property.equals(o.property) && range.equals(o.range);
  }
  
  @Override
  public int hashCode() {
    return 2 * bound.hashCode() + 3 * property.hashCode() + 5 * range.hashCode();
  }
  
  public DataMinCardinality withBound(java.math.BigInteger bound) {
    return new DataMinCardinality(bound, property, range);
  }
  
  public DataMinCardinality withProperty(hydra.langs.owl.syntax.DataPropertyExpression property) {
    return new DataMinCardinality(bound, property, range);
  }
  
  public DataMinCardinality withRange(java.util.List<hydra.langs.owl.syntax.DataRange> range) {
    return new DataMinCardinality(bound, property, range);
  }
}