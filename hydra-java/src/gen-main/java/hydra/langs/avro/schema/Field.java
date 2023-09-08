package hydra.langs.avro.schema;

import java.io.Serializable;

public class Field implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/avro/schema.Field");
  
  /**
   * a JSON string providing the name of the field
   */
  public final String name;
  
  /**
   * a JSON string describing this field for users
   */
  public final java.util.Optional<String> doc;
  
  /**
   * a schema
   */
  public final hydra.langs.avro.schema.Schema type;
  
  /**
   * default value for this field, only used when reading instances that lack the field for schema evolution purposes
   */
  public final java.util.Optional<hydra.json.Value> default_;
  
  /**
   * specifies how this field impacts sort ordering of this record
   */
  public final java.util.Optional<hydra.langs.avro.schema.Order> order;
  
  /**
   * a JSON array of strings, providing alternate names for this field
   */
  public final java.util.Optional<java.util.List<String>> aliases;
  
  /**
   * Any additional key/value pairs attached to the field
   */
  public final java.util.Map<String, hydra.json.Value> annotations;
  
  public Field (String name, java.util.Optional<String> doc, hydra.langs.avro.schema.Schema type, java.util.Optional<hydra.json.Value> default_, java.util.Optional<hydra.langs.avro.schema.Order> order, java.util.Optional<java.util.List<String>> aliases, java.util.Map<String, hydra.json.Value> annotations) {
    this.name = name;
    this.doc = doc;
    this.type = type;
    this.default_ = default_;
    this.order = order;
    this.aliases = aliases;
    this.annotations = annotations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Field)) {
      return false;
    }
    Field o = (Field) (other);
    return name.equals(o.name) && doc.equals(o.doc) && type.equals(o.type) && default_.equals(o.default_) && order.equals(o.order) && aliases.equals(o.aliases) && annotations.equals(o.annotations);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * doc.hashCode() + 5 * type.hashCode() + 7 * default_.hashCode() + 11 * order.hashCode() + 13 * aliases.hashCode() + 17 * annotations.hashCode();
  }
  
  public Field withName(String name) {
    return new Field(name, doc, type, default_, order, aliases, annotations);
  }
  
  public Field withDoc(java.util.Optional<String> doc) {
    return new Field(name, doc, type, default_, order, aliases, annotations);
  }
  
  public Field withType(hydra.langs.avro.schema.Schema type) {
    return new Field(name, doc, type, default_, order, aliases, annotations);
  }
  
  public Field withDefault(java.util.Optional<hydra.json.Value> default_) {
    return new Field(name, doc, type, default_, order, aliases, annotations);
  }
  
  public Field withOrder(java.util.Optional<hydra.langs.avro.schema.Order> order) {
    return new Field(name, doc, type, default_, order, aliases, annotations);
  }
  
  public Field withAliases(java.util.Optional<java.util.List<String>> aliases) {
    return new Field(name, doc, type, default_, order, aliases, annotations);
  }
  
  public Field withAnnotations(java.util.Map<String, hydra.json.Value> annotations) {
    return new Field(name, doc, type, default_, order, aliases, annotations);
  }
}