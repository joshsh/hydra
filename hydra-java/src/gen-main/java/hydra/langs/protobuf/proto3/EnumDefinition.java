package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * Enum type definition
 */
public class EnumDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.EnumDefinition");
  
  /**
   * Enum type name
   */
  public final hydra.langs.protobuf.proto3.TypeName name;
  
  /**
   * Enum value definitions
   */
  public final java.util.List<hydra.langs.protobuf.proto3.EnumValue> values;
  
  /**
   * Protocol buffer options
   */
  public final java.util.List<hydra.langs.protobuf.proto3.Option> options;
  
  public EnumDefinition (hydra.langs.protobuf.proto3.TypeName name, java.util.List<hydra.langs.protobuf.proto3.EnumValue> values, java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    this.name = name;
    this.values = values;
    this.options = options;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumDefinition)) {
      return false;
    }
    EnumDefinition o = (EnumDefinition) (other);
    return name.equals(o.name) && values.equals(o.values) && options.equals(o.options);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * values.hashCode() + 5 * options.hashCode();
  }
  
  public EnumDefinition withName(hydra.langs.protobuf.proto3.TypeName name) {
    return new EnumDefinition(name, values, options);
  }
  
  public EnumDefinition withValues(java.util.List<hydra.langs.protobuf.proto3.EnumValue> values) {
    return new EnumDefinition(name, values, options);
  }
  
  public EnumDefinition withOptions(java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    return new EnumDefinition(name, values, options);
  }
}