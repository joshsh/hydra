// Note: this is an automatically generated file. Do not edit.

package hydra.langs.pegasus.pdl;

import java.io.Serializable;

public class NamedSchema implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.NamedSchema");
  
  public final hydra.langs.pegasus.pdl.QualifiedName qualifiedName;
  
  public final hydra.langs.pegasus.pdl.NamedSchema_Type type;
  
  public final hydra.langs.pegasus.pdl.Annotations annotations;
  
  public NamedSchema (hydra.langs.pegasus.pdl.QualifiedName qualifiedName, hydra.langs.pegasus.pdl.NamedSchema_Type type, hydra.langs.pegasus.pdl.Annotations annotations) {
    if (qualifiedName == null) {
      throw new IllegalArgumentException("null value for 'qualifiedName' argument");
    }
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    if (annotations == null) {
      throw new IllegalArgumentException("null value for 'annotations' argument");
    }
    this.qualifiedName = qualifiedName;
    this.type = type;
    this.annotations = annotations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NamedSchema)) {
      return false;
    }
    NamedSchema o = (NamedSchema) (other);
    return qualifiedName.equals(o.qualifiedName) && type.equals(o.type) && annotations.equals(o.annotations);
  }
  
  @Override
  public int hashCode() {
    return 2 * qualifiedName.hashCode() + 3 * type.hashCode() + 5 * annotations.hashCode();
  }
  
  public NamedSchema withQualifiedName(hydra.langs.pegasus.pdl.QualifiedName qualifiedName) {
    if (qualifiedName == null) {
      throw new IllegalArgumentException("null value for 'qualifiedName' argument");
    }
    return new NamedSchema(qualifiedName, type, annotations);
  }
  
  public NamedSchema withType(hydra.langs.pegasus.pdl.NamedSchema_Type type) {
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    return new NamedSchema(qualifiedName, type, annotations);
  }
  
  public NamedSchema withAnnotations(hydra.langs.pegasus.pdl.Annotations annotations) {
    if (annotations == null) {
      throw new IllegalArgumentException("null value for 'annotations' argument");
    }
    return new NamedSchema(qualifiedName, type, annotations);
  }
}