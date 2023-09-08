package hydra.langs.pegasus.pdl;

import java.io.Serializable;

public class RecordSchema implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.RecordSchema");
  
  public final java.util.List<hydra.langs.pegasus.pdl.RecordField> fields;
  
  public final java.util.List<hydra.langs.pegasus.pdl.NamedSchema> includes;
  
  public RecordSchema (java.util.List<hydra.langs.pegasus.pdl.RecordField> fields, java.util.List<hydra.langs.pegasus.pdl.NamedSchema> includes) {
    this.fields = fields;
    this.includes = includes;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RecordSchema)) {
      return false;
    }
    RecordSchema o = (RecordSchema) (other);
    return fields.equals(o.fields) && includes.equals(o.includes);
  }
  
  @Override
  public int hashCode() {
    return 2 * fields.hashCode() + 3 * includes.hashCode();
  }
  
  public RecordSchema withFields(java.util.List<hydra.langs.pegasus.pdl.RecordField> fields) {
    return new RecordSchema(fields, includes);
  }
  
  public RecordSchema withIncludes(java.util.List<hydra.langs.pegasus.pdl.NamedSchema> includes) {
    return new RecordSchema(fields, includes);
  }
}