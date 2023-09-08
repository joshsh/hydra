package hydra.langs.avro.schema;

import java.io.Serializable;

public class Fixed implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/avro/schema.Fixed");
  
  /**
   * an integer, specifying the number of bytes per value
   */
  public final Integer size;
  
  public Fixed (Integer size) {
    this.size = size;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Fixed)) {
      return false;
    }
    Fixed o = (Fixed) (other);
    return size.equals(o.size);
  }
  
  @Override
  public int hashCode() {
    return 2 * size.hashCode();
  }
}