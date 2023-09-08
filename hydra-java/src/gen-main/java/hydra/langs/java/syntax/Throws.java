package hydra.langs.java.syntax;

import java.io.Serializable;

public class Throws implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Throws");
  
  public final java.util.List<hydra.langs.java.syntax.ExceptionType> value;
  
  public Throws (java.util.List<hydra.langs.java.syntax.ExceptionType> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Throws)) {
      return false;
    }
    Throws o = (Throws) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}