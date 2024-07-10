// Note: this is an automatically generated file. Do not edit.

package hydra.langs.pegasus.pdl;

import java.io.Serializable;

public class FieldName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.FieldName");
  
  public final String value;
  
  public FieldName (String value) {
    if (value == null) {
      throw new IllegalArgumentException("null value for 'value' argument");
    }
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldName)) {
      return false;
    }
    FieldName o = (FieldName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}