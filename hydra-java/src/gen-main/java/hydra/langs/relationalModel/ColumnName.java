package hydra.langs.relationalModel;

import java.io.Serializable;

/**
 * A name for a domain which serves to identify the role played by that domain in the given relation; a 'role name' in Codd
 */
public class ColumnName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/relationalModel.ColumnName");
  
  /**
   * A name for a domain which serves to identify the role played by that domain in the given relation; a 'role name' in Codd
   */
  public final String value;
  
  public ColumnName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnName)) {
      return false;
    }
    ColumnName o = (ColumnName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}