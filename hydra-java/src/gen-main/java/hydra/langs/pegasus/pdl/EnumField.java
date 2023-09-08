package hydra.langs.pegasus.pdl;

import java.io.Serializable;

public class EnumField implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.EnumField");
  
  public final hydra.langs.pegasus.pdl.EnumFieldName name;
  
  public final hydra.langs.pegasus.pdl.Annotations annotations;
  
  public EnumField (hydra.langs.pegasus.pdl.EnumFieldName name, hydra.langs.pegasus.pdl.Annotations annotations) {
    this.name = name;
    this.annotations = annotations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumField)) {
      return false;
    }
    EnumField o = (EnumField) (other);
    return name.equals(o.name) && annotations.equals(o.annotations);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * annotations.hashCode();
  }
  
  public EnumField withName(hydra.langs.pegasus.pdl.EnumFieldName name) {
    return new EnumField(name, annotations);
  }
  
  public EnumField withAnnotations(hydra.langs.pegasus.pdl.Annotations annotations) {
    return new EnumField(name, annotations);
  }
}