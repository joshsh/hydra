package hydra.langs.java.syntax;

import java.io.Serializable;

public class ModuleDirective_Provides implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ModuleDirective.Provides");
  
  public final hydra.langs.java.syntax.TypeName to;
  
  /**
   * At least one type
   */
  public final java.util.List<hydra.langs.java.syntax.TypeName> with;
  
  public ModuleDirective_Provides (hydra.langs.java.syntax.TypeName to, java.util.List<hydra.langs.java.syntax.TypeName> with) {
    this.to = to;
    this.with = with;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ModuleDirective_Provides)) {
      return false;
    }
    ModuleDirective_Provides o = (ModuleDirective_Provides) (other);
    return to.equals(o.to) && with.equals(o.with);
  }
  
  @Override
  public int hashCode() {
    return 2 * to.hashCode() + 3 * with.hashCode();
  }
  
  public ModuleDirective_Provides withTo(hydra.langs.java.syntax.TypeName to) {
    return new ModuleDirective_Provides(to, with);
  }
  
  public ModuleDirective_Provides withWith(java.util.List<hydra.langs.java.syntax.TypeName> with) {
    return new ModuleDirective_Provides(to, with);
  }
}