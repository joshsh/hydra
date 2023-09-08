package hydra.langs.relationalModel;

import java.io.Serializable;

/**
 * An n-tuple which is an element of a given relation
 */
public class Row<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/relationalModel.Row");
  
  public final java.util.List<V> value;
  
  public Row (java.util.List<V> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Row)) {
      return false;
    }
    Row o = (Row) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}