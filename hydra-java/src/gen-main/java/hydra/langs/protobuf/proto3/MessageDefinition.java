package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * A protocol buffer message type
 */
public class MessageDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.MessageDefinition");
  
  /**
   * The fully qualified message name
   */
  public final hydra.langs.protobuf.proto3.TypeName name;
  
  /**
   * The list of fields
   */
  public final java.util.List<hydra.langs.protobuf.proto3.Field> fields;
  
  /**
   * The protocol buffer options
   */
  public final java.util.List<hydra.langs.protobuf.proto3.Option> options;
  
  public MessageDefinition (hydra.langs.protobuf.proto3.TypeName name, java.util.List<hydra.langs.protobuf.proto3.Field> fields, java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    this.name = name;
    this.fields = fields;
    this.options = options;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MessageDefinition)) {
      return false;
    }
    MessageDefinition o = (MessageDefinition) (other);
    return name.equals(o.name) && fields.equals(o.fields) && options.equals(o.options);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * fields.hashCode() + 5 * options.hashCode();
  }
  
  public MessageDefinition withName(hydra.langs.protobuf.proto3.TypeName name) {
    return new MessageDefinition(name, fields, options);
  }
  
  public MessageDefinition withFields(java.util.List<hydra.langs.protobuf.proto3.Field> fields) {
    return new MessageDefinition(name, fields, options);
  }
  
  public MessageDefinition withOptions(java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    return new MessageDefinition(name, fields, options);
  }
}