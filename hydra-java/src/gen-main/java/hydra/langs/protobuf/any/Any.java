package hydra.langs.protobuf.any;

import java.io.Serializable;

/**
 * `Any` contains an arbitrary serialized protocol buffer message along with a URL that describes the type of the serialized message.
 */
public class Any implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/any.Any");
  
  /**
   * A URL/resource name that uniquely identifies the type of the serialized protocol buffer message.
   */
  public final String typeUrl;
  
  public final String value;
  
  public Any (String typeUrl, String value) {
    this.typeUrl = typeUrl;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Any)) {
      return false;
    }
    Any o = (Any) (other);
    return typeUrl.equals(o.typeUrl) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeUrl.hashCode() + 3 * value.hashCode();
  }
  
  public Any withTypeUrl(String typeUrl) {
    return new Any(typeUrl, value);
  }
  
  public Any withValue(String value) {
    return new Any(typeUrl, value);
  }
}