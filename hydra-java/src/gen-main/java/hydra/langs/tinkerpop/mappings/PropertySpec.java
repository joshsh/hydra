package hydra.langs.tinkerpop.mappings;

import java.io.Serializable;

/**
 * A mapping specification producing properties of a specified key, and values of the appropriate type.
 */
public class PropertySpec implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/mappings.PropertySpec");
  
  /**
   * The key of the target properties
   */
  public final hydra.langs.tinkerpop.propertyGraph.PropertyKey key;
  
  /**
   * A specification of the value of each target property, which must conform to the type associated with the property key
   */
  public final hydra.langs.tinkerpop.mappings.ValueSpec value;
  
  public PropertySpec (hydra.langs.tinkerpop.propertyGraph.PropertyKey key, hydra.langs.tinkerpop.mappings.ValueSpec value) {
    this.key = key;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PropertySpec)) {
      return false;
    }
    PropertySpec o = (PropertySpec) (other);
    return key.equals(o.key) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * key.hashCode() + 3 * value.hashCode();
  }
  
  public PropertySpec withKey(hydra.langs.tinkerpop.propertyGraph.PropertyKey key) {
    return new PropertySpec(key, value);
  }
  
  public PropertySpec withValue(hydra.langs.tinkerpop.mappings.ValueSpec value) {
    return new PropertySpec(key, value);
  }
}