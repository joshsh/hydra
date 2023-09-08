package hydra.core;

import java.io.Serializable;

/**
 * A map type
 */
public class MapType<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.MapType");
  
  public final hydra.core.Type<A> keys;
  
  public final hydra.core.Type<A> values;
  
  public MapType (hydra.core.Type<A> keys, hydra.core.Type<A> values) {
    this.keys = keys;
    this.values = values;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MapType)) {
      return false;
    }
    MapType o = (MapType) (other);
    return keys.equals(o.keys) && values.equals(o.values);
  }
  
  @Override
  public int hashCode() {
    return 2 * keys.hashCode() + 3 * values.hashCode();
  }
  
  public MapType withKeys(hydra.core.Type<A> keys) {
    return new MapType(keys, values);
  }
  
  public MapType withValues(hydra.core.Type<A> values) {
    return new MapType(keys, values);
  }
}