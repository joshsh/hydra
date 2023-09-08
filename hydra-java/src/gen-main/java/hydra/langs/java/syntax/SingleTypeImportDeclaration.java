package hydra.langs.java.syntax;

import java.io.Serializable;

public class SingleTypeImportDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.SingleTypeImportDeclaration");
  
  public final hydra.langs.java.syntax.TypeName value;
  
  public SingleTypeImportDeclaration (hydra.langs.java.syntax.TypeName value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SingleTypeImportDeclaration)) {
      return false;
    }
    SingleTypeImportDeclaration o = (SingleTypeImportDeclaration) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}