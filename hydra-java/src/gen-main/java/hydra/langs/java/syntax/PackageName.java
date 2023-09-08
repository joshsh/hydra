package hydra.langs.java.syntax;

import java.io.Serializable;

public class PackageName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.PackageName");
  
  public final java.util.List<hydra.langs.java.syntax.Identifier> value;
  
  public PackageName (java.util.List<hydra.langs.java.syntax.Identifier> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PackageName)) {
      return false;
    }
    PackageName o = (PackageName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}