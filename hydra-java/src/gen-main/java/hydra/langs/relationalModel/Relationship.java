package hydra.langs.relationalModel;

import java.io.Serializable;

/**
 * A domain-unordered (string-indexed, rather than position-indexed) relation
 */
public class Relationship<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/relationalModel.Relationship");
  
  public final java.util.Set<java.util.Map<hydra.langs.relationalModel.ColumnName, V>> value;
  
  public Relationship (java.util.Set<java.util.Map<hydra.langs.relationalModel.ColumnName, V>> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Relationship)) {
      return false;
    }
    Relationship o = (Relationship) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}