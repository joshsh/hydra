// Note: this is an automatically generated file. Do not edit.

package hydra.langs.pegasus.pdl;

import java.io.Serializable;

/**
 * Annotations which can be applied to record fields, aliased union members, enum symbols, or named schemas
 */
public class Annotations implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.Annotations");
  
  public final java.util.Optional<String> doc;
  
  public final Boolean deprecated;
  
  public Annotations (java.util.Optional<String> doc, Boolean deprecated) {
    if (doc == null) {
      throw new IllegalArgumentException("null value for 'doc' argument");
    }
    if (deprecated == null) {
      throw new IllegalArgumentException("null value for 'deprecated' argument");
    }
    this.doc = doc;
    this.deprecated = deprecated;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Annotations)) {
      return false;
    }
    Annotations o = (Annotations) (other);
    return doc.equals(o.doc) && deprecated.equals(o.deprecated);
  }
  
  @Override
  public int hashCode() {
    return 2 * doc.hashCode() + 3 * deprecated.hashCode();
  }
  
  public Annotations withDoc(java.util.Optional<String> doc) {
    if (doc == null) {
      throw new IllegalArgumentException("null value for 'doc' argument");
    }
    return new Annotations(doc, deprecated);
  }
  
  public Annotations withDeprecated(Boolean deprecated) {
    if (deprecated == null) {
      throw new IllegalArgumentException("null value for 'deprecated' argument");
    }
    return new Annotations(doc, deprecated);
  }
}