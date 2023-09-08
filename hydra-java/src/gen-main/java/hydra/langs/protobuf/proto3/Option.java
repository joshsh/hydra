package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * A protocol buffer option, which can be attached to a message, field, enumeration, etc
 */
public class Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.Option");
  
  /**
   * The option's name. For protobuf built-in options (options defined in descriptor.proto), this is the short name. For example, `"map_entry"`. For custom options, it should be the fully-qualified name. For example, `"google.api.http"`.
   */
  public final String name;
  
  /**
   * The option's value
   */
  public final String value;
  
  public Option (String name, String value) {
    this.name = name;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Option)) {
      return false;
    }
    Option o = (Option) (other);
    return name.equals(o.name) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * value.hashCode();
  }
  
  public Option withName(String name) {
    return new Option(name, value);
  }
  
  public Option withValue(String value) {
    return new Option(name, value);
  }
}