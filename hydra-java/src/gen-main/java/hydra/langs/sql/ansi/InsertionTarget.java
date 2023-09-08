package hydra.langs.sql.ansi;

import java.io.Serializable;

public class InsertionTarget implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.InsertionTarget");
  
  public final hydra.langs.sql.ansi.TableName value;
  
  public InsertionTarget (hydra.langs.sql.ansi.TableName value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InsertionTarget)) {
      return false;
    }
    InsertionTarget o = (InsertionTarget) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}