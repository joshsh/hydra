// Note: this is an automatically generated file. Do not edit.

package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * Enum value definition
 */
public class EnumValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.EnumValue");
  
  /**
   * Enum value name
   */
  public final hydra.langs.protobuf.proto3.EnumValueName name;
  
  /**
   * Enum value number
   */
  public final Integer number;
  
  /**
   * Protocol buffer options
   */
  public final java.util.List<hydra.langs.protobuf.proto3.Option> options;
  
  public EnumValue (hydra.langs.protobuf.proto3.EnumValueName name, Integer number, java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    if (number == null) {
      throw new IllegalArgumentException("null value for 'number' argument");
    }
    if (options == null) {
      throw new IllegalArgumentException("null value for 'options' argument");
    }
    this.name = name;
    this.number = number;
    this.options = options;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumValue)) {
      return false;
    }
    EnumValue o = (EnumValue) (other);
    return name.equals(o.name) && number.equals(o.number) && options.equals(o.options);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * number.hashCode() + 5 * options.hashCode();
  }
  
  public EnumValue withName(hydra.langs.protobuf.proto3.EnumValueName name) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new EnumValue(name, number, options);
  }
  
  public EnumValue withNumber(Integer number) {
    if (number == null) {
      throw new IllegalArgumentException("null value for 'number' argument");
    }
    return new EnumValue(name, number, options);
  }
  
  public EnumValue withOptions(java.util.List<hydra.langs.protobuf.proto3.Option> options) {
    if (options == null) {
      throw new IllegalArgumentException("null value for 'options' argument");
    }
    return new EnumValue(name, number, options);
  }
}