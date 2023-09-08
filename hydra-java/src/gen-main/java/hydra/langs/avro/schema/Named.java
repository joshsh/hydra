package hydra.langs.avro.schema;

import java.io.Serializable;

public class Named implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/avro/schema.Named");
  
  /**
   * a string naming this schema
   */
  public final String name;
  
  /**
   * a string that qualifies the name
   */
  public final java.util.Optional<String> namespace;
  
  /**
   * a JSON array of strings, providing alternate names for this schema
   */
  public final java.util.Optional<java.util.List<String>> aliases;
  
  /**
   * a JSON string providing documentation to the user of this schema
   */
  public final java.util.Optional<String> doc;
  
  public final hydra.langs.avro.schema.NamedType type;
  
  /**
   * Any additional key/value pairs attached to the type
   */
  public final java.util.Map<String, hydra.json.Value> annotations;
  
  public Named (String name, java.util.Optional<String> namespace, java.util.Optional<java.util.List<String>> aliases, java.util.Optional<String> doc, hydra.langs.avro.schema.NamedType type, java.util.Map<String, hydra.json.Value> annotations) {
    this.name = name;
    this.namespace = namespace;
    this.aliases = aliases;
    this.doc = doc;
    this.type = type;
    this.annotations = annotations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Named)) {
      return false;
    }
    Named o = (Named) (other);
    return name.equals(o.name) && namespace.equals(o.namespace) && aliases.equals(o.aliases) && doc.equals(o.doc) && type.equals(o.type) && annotations.equals(o.annotations);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * namespace.hashCode() + 5 * aliases.hashCode() + 7 * doc.hashCode() + 11 * type.hashCode() + 13 * annotations.hashCode();
  }
  
  public Named withName(String name) {
    return new Named(name, namespace, aliases, doc, type, annotations);
  }
  
  public Named withNamespace(java.util.Optional<String> namespace) {
    return new Named(name, namespace, aliases, doc, type, annotations);
  }
  
  public Named withAliases(java.util.Optional<java.util.List<String>> aliases) {
    return new Named(name, namespace, aliases, doc, type, annotations);
  }
  
  public Named withDoc(java.util.Optional<String> doc) {
    return new Named(name, namespace, aliases, doc, type, annotations);
  }
  
  public Named withType(hydra.langs.avro.schema.NamedType type) {
    return new Named(name, namespace, aliases, doc, type, annotations);
  }
  
  public Named withAnnotations(java.util.Map<String, hydra.json.Value> annotations) {
    return new Named(name, namespace, aliases, doc, type, annotations);
  }
}