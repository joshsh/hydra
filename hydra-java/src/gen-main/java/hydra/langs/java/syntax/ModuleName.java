package hydra.langs.java.syntax;

import java.io.Serializable;

public class ModuleName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ModuleName");
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public final java.util.Optional<hydra.langs.java.syntax.ModuleName> name;
  
  public ModuleName (hydra.langs.java.syntax.Identifier identifier, java.util.Optional<hydra.langs.java.syntax.ModuleName> name) {
    this.identifier = identifier;
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ModuleName)) {
      return false;
    }
    ModuleName o = (ModuleName) (other);
    return identifier.equals(o.identifier) && name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * identifier.hashCode() + 3 * name.hashCode();
  }
  
  public ModuleName withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new ModuleName(identifier, name);
  }
  
  public ModuleName withName(java.util.Optional<hydra.langs.java.syntax.ModuleName> name) {
    return new ModuleName(identifier, name);
  }
}