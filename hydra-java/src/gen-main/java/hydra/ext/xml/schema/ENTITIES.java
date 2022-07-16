package hydra.ext.xml.schema;

public class ENTITIES {
  public final String value;
  
  public ENTITIES (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ENTITIES)) {
      return false;
    }
    ENTITIES o = (ENTITIES) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}