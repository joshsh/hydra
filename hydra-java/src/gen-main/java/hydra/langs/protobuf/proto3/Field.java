package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * A single field of a message type
 */
public class Field implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.Field");
  
  /**
   * The field name
   */
  public final hydra.langs.protobuf.proto3.FieldName name;
  
  /**
   * The field JSON name
   */
  public final java.util.Optional<String> jsonName;
  
  /**
   * The datatype of the field
   */
  public final hydra.langs.protobuf.proto3.FieldType type;
  
  /**
   * The field number
   */
  public final Integer number;
  
  /**
   * The protocol buffer options
   */
  public final java.util.List<hydra.langs.protobuf.proto3.Option> options;
  
  public Field (hydra.langs.protobuf.proto3.FieldName name, java.util.Optional<String> jsonName, hydra.langs.protobuf.proto3.FieldType type, Integer number, java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    this.name = name;
    this.jsonName = jsonName;
    this.type = type;
    this.number = number;
    this.options = options;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Field)) {
      return false;
    }
    Field o = (Field) (other);
    return name.equals(o.name) && jsonName.equals(o.jsonName) && type.equals(o.type) && number.equals(o.number) && options.equals(o.options);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * jsonName.hashCode() + 5 * type.hashCode() + 7 * number.hashCode() + 11 * options.hashCode();
  }
  
  public Field withName(hydra.langs.protobuf.proto3.FieldName name) {
    return new Field(name, jsonName, type, number, options);
  }
  
  public Field withJsonName(java.util.Optional<String> jsonName) {
    return new Field(name, jsonName, type, number, options);
  }
  
  public Field withType(hydra.langs.protobuf.proto3.FieldType type) {
    return new Field(name, jsonName, type, number, options);
  }
  
  public Field withNumber(Integer number) {
    return new Field(name, jsonName, type, number, options);
  }
  
  public Field withOptions(java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    return new Field(name, jsonName, type, number, options);
  }
}