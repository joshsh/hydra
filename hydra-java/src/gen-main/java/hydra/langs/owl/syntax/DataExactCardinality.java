package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DataExactCardinality implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DataExactCardinality");
  
  public final java.math.BigInteger bound;
  
  public final hydra.langs.owl.syntax.DataPropertyExpression property;
  
  public final java.util.List<hydra.langs.owl.syntax.DataRange> range;
  
  public DataExactCardinality (java.math.BigInteger bound, hydra.langs.owl.syntax.DataPropertyExpression property, java.util.List<hydra.langs.owl.syntax.DataRange> range) {
    this.bound = bound;
    this.property = property;
    this.range = range;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataExactCardinality)) {
      return false;
    }
    DataExactCardinality o = (DataExactCardinality) (other);
    return bound.equals(o.bound) && property.equals(o.property) && range.equals(o.range);
  }
  
  @Override
  public int hashCode() {
    return 2 * bound.hashCode() + 3 * property.hashCode() + 5 * range.hashCode();
  }
  
  public DataExactCardinality withBound(java.math.BigInteger bound) {
    return new DataExactCardinality(bound, property, range);
  }
  
  public DataExactCardinality withProperty(hydra.langs.owl.syntax.DataPropertyExpression property) {
    return new DataExactCardinality(bound, property, range);
  }
  
  public DataExactCardinality withRange(java.util.List<hydra.langs.owl.syntax.DataRange> range) {
    return new DataExactCardinality(bound, property, range);
  }
}