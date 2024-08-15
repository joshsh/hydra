// Note: this is an automatically generated file. Do not edit.

package hydra.langs.relationalModel;

import java.io.Serializable;

/**
 * A unique relation (table) name
 */
public class RelationName implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/relationalModel.RelationName");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final String value;
  
  public RelationName (String value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RelationName)) {
      return false;
    }
    RelationName o = (RelationName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}