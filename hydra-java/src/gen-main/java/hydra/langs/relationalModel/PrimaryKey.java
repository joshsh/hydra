package hydra.langs.relationalModel;

import java.io.Serializable;

/**
 * A primary key of a relation, specified either as a single column, or as a list of columns
 */
public class PrimaryKey implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/relationalModel.PrimaryKey");
  
  /**
   * A primary key of a relation, specified either as a single column, or as a list of columns
   */
  public final java.util.List<hydra.langs.relationalModel.ColumnName> value;
  
  public PrimaryKey (java.util.List<hydra.langs.relationalModel.ColumnName> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PrimaryKey)) {
      return false;
    }
    PrimaryKey o = (PrimaryKey) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}