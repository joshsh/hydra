package hydra.langs.java.syntax;

import java.io.Serializable;

public class ModuleDirective_ExportsOrOpens implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ModuleDirective.ExportsOrOpens");
  
  public final hydra.langs.java.syntax.PackageName package_;
  
  /**
   * At least one module
   */
  public final java.util.List<hydra.langs.java.syntax.ModuleName> modules;
  
  public ModuleDirective_ExportsOrOpens (hydra.langs.java.syntax.PackageName package_, java.util.List<hydra.langs.java.syntax.ModuleName> modules) {
    this.package_ = package_;
    this.modules = modules;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ModuleDirective_ExportsOrOpens)) {
      return false;
    }
    ModuleDirective_ExportsOrOpens o = (ModuleDirective_ExportsOrOpens) (other);
    return package_.equals(o.package_) && modules.equals(o.modules);
  }
  
  @Override
  public int hashCode() {
    return 2 * package_.hashCode() + 3 * modules.hashCode();
  }
  
  public ModuleDirective_ExportsOrOpens withPackage(hydra.langs.java.syntax.PackageName package_) {
    return new ModuleDirective_ExportsOrOpens(package_, modules);
  }
  
  public ModuleDirective_ExportsOrOpens withModules(java.util.List<hydra.langs.java.syntax.ModuleName> modules) {
    return new ModuleDirective_ExportsOrOpens(package_, modules);
  }
}