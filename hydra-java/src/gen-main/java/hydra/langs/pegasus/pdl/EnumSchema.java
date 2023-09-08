package hydra.langs.pegasus.pdl;

import java.io.Serializable;

public class EnumSchema implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.EnumSchema");
  
  public final java.util.List<hydra.langs.pegasus.pdl.EnumField> fields;
  
  public EnumSchema (java.util.List<hydra.langs.pegasus.pdl.EnumField> fields) {
    this.fields = fields;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumSchema)) {
      return false;
    }
    EnumSchema o = (EnumSchema) (other);
    return fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * fields.hashCode();
  }
}