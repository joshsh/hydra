package hydra.langs.relationalModel;

import java.io.Serializable;

/**
 * A set of distinct n-tuples; a table
 */
public class Relation<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/relationalModel.Relation");
  
  public final java.util.Set<java.util.List<V>> value;
  
  public Relation (java.util.Set<java.util.List<V>> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Relation)) {
      return false;
    }
    Relation o = (Relation) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}