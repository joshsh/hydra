package hydra.langs.java.syntax;

import java.io.Serializable;

public class StaticImportOnDemandDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.StaticImportOnDemandDeclaration");
  
  public final hydra.langs.java.syntax.TypeName value;
  
  public StaticImportOnDemandDeclaration (hydra.langs.java.syntax.TypeName value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StaticImportOnDemandDeclaration)) {
      return false;
    }
    StaticImportOnDemandDeclaration o = (StaticImportOnDemandDeclaration) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}