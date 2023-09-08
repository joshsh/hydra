package hydra.langs.java.syntax;

import java.io.Serializable;

public class PackageOrTypeName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.PackageOrTypeName");
  
  public final java.util.List<hydra.langs.java.syntax.Identifier> value;
  
  public PackageOrTypeName (java.util.List<hydra.langs.java.syntax.Identifier> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PackageOrTypeName)) {
      return false;
    }
    PackageOrTypeName o = (PackageOrTypeName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}