package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Wrapper struct to store key values
 */
public class KeyValue implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.KeyValue");
  
  public final String key;
  
  public final java.util.Optional<String> value;
  
  public KeyValue (String key, java.util.Optional<String> value) {
    this.key = key;
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof KeyValue)) {
      return false;
    }
    KeyValue o = (KeyValue) (other);
    return key.equals(o.key) && value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * key.hashCode() + 3 * value.hashCode();
  }
  
  public KeyValue withKey(String key) {
    return new KeyValue(key, value);
  }
  
  public KeyValue withValue(java.util.Optional<String> value) {
    return new KeyValue(key, value);
  }
}