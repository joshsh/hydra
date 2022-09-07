package hydra.ext.xml.schema;

public class HexBinary {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/xml/schema.HexBinary");
  
  public final String value;
  
  public HexBinary (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof HexBinary)) {
      return false;
    }
    HexBinary o = (HexBinary) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}