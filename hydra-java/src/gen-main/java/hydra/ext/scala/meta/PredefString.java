package hydra.ext.scala.meta;

public class PredefString {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/scala/meta.PredefString");
  
  public final String value;
  
  public PredefString (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PredefString)) {
      return false;
    }
    PredefString o = (PredefString) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}