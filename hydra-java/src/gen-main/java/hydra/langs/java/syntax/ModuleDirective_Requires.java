package hydra.langs.java.syntax;

import java.io.Serializable;

public class ModuleDirective_Requires implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ModuleDirective.Requires");
  
  public final java.util.List<hydra.langs.java.syntax.RequiresModifier> modifiers;
  
  public final hydra.langs.java.syntax.ModuleName module;
  
  public ModuleDirective_Requires (java.util.List<hydra.langs.java.syntax.RequiresModifier> modifiers, hydra.langs.java.syntax.ModuleName module) {
    this.modifiers = modifiers;
    this.module = module;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ModuleDirective_Requires)) {
      return false;
    }
    ModuleDirective_Requires o = (ModuleDirective_Requires) (other);
    return modifiers.equals(o.modifiers) && module.equals(o.module);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * module.hashCode();
  }
  
  public ModuleDirective_Requires withModifiers(java.util.List<hydra.langs.java.syntax.RequiresModifier> modifiers) {
    return new ModuleDirective_Requires(modifiers, module);
  }
  
  public ModuleDirective_Requires withModule(hydra.langs.java.syntax.ModuleName module) {
    return new ModuleDirective_Requires(modifiers, module);
  }
}