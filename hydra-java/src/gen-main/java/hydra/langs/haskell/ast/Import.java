// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * An import statement
 */
public class Import implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Import");
  
  public final Boolean qualified;
  
  public final hydra.langs.haskell.ast.ModuleName module;
  
  public final java.util.Optional<hydra.langs.haskell.ast.ModuleName> as;
  
  public final java.util.Optional<hydra.langs.haskell.ast.Import_Spec> spec;
  
  public Import (Boolean qualified, hydra.langs.haskell.ast.ModuleName module, java.util.Optional<hydra.langs.haskell.ast.ModuleName> as, java.util.Optional<hydra.langs.haskell.ast.Import_Spec> spec) {
    if (qualified == null) {
      throw new IllegalArgumentException("null value for 'qualified' argument");
    }
    if (module == null) {
      throw new IllegalArgumentException("null value for 'module' argument");
    }
    if (as == null) {
      throw new IllegalArgumentException("null value for 'as' argument");
    }
    if (spec == null) {
      throw new IllegalArgumentException("null value for 'spec' argument");
    }
    this.qualified = qualified;
    this.module = module;
    this.as = as;
    this.spec = spec;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Import)) {
      return false;
    }
    Import o = (Import) (other);
    return qualified.equals(o.qualified) && module.equals(o.module) && as.equals(o.as) && spec.equals(o.spec);
  }
  
  @Override
  public int hashCode() {
    return 2 * qualified.hashCode() + 3 * module.hashCode() + 5 * as.hashCode() + 7 * spec.hashCode();
  }
  
  public Import withQualified(Boolean qualified) {
    if (qualified == null) {
      throw new IllegalArgumentException("null value for 'qualified' argument");
    }
    return new Import(qualified, module, as, spec);
  }
  
  public Import withModule(hydra.langs.haskell.ast.ModuleName module) {
    if (module == null) {
      throw new IllegalArgumentException("null value for 'module' argument");
    }
    return new Import(qualified, module, as, spec);
  }
  
  public Import withAs(java.util.Optional<hydra.langs.haskell.ast.ModuleName> as) {
    if (as == null) {
      throw new IllegalArgumentException("null value for 'as' argument");
    }
    return new Import(qualified, module, as, spec);
  }
  
  public Import withSpec(java.util.Optional<hydra.langs.haskell.ast.Import_Spec> spec) {
    if (spec == null) {
      throw new IllegalArgumentException("null value for 'spec' argument");
    }
    return new Import(qualified, module, as, spec);
  }
}