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
    return new Annotations(doc, deprecated);
  }
  
  public Annotations withDeprecated(Boolean deprecated) {
    return new Annotations(doc, deprecated);
  }
}