package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * A key/value property
 */
public class Property<V> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.Property");
  
  /**
   * They key of the property
   */
  public final hydra.langs.tinkerpop.propertyGraph.PropertyKey key;
  
  /**
   * The value of the property
   */
  public final V value;
  
  public Property (hydra.langs.tinkerpop.propertyGraph.PropertyKey key, V value) {
    this.key = key;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Property)) {
      return false;
    }
    Property o = (Property) (other);
    return key.equals(o.key) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * key.hashCode() + 3 * value.hashCode();
  }
  
  public Property withKey(hydra.langs.tinkerpop.propertyGraph.PropertyKey key) {
    return new Property(key, value);
  }
  
  public Property withValue(V value) {
    return new Property(key, value);
  }
}