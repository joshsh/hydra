package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * A property key
 */
public class PropertyKey implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.PropertyKey");
  
  /**
   * A property key
   */
  public final String value;
  
  public PropertyKey (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PropertyKey)) {
      return false;
    }
    PropertyKey o = (PropertyKey) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}