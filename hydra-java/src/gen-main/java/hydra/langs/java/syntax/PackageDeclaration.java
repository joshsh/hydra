package hydra.langs.java.syntax;

import java.io.Serializable;

public class PackageDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.PackageDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.PackageModifier> modifiers;
  
  public final java.util.List<hydra.langs.java.syntax.Identifier> identifiers;
  
  public PackageDeclaration (java.util.List<hydra.langs.java.syntax.PackageModifier> modifiers, java.util.List<hydra.langs.java.syntax.Identifier> identifiers) {
    this.modifiers = modifiers;
    this.identifiers = identifiers;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PackageDeclaration)) {
      return false;
    }
    PackageDeclaration o = (PackageDeclaration) (other);
    return modifiers.equals(o.modifiers) && identifiers.equals(o.identifiers);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * identifiers.hashCode();
  }
  
  public PackageDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.PackageModifier> modifiers) {
    return new PackageDeclaration(modifiers, identifiers);
  }
  
  public PackageDeclaration withIdentifiers(java.util.List<hydra.langs.java.syntax.Identifier> identifiers) {
    return new PackageDeclaration(modifiers, identifiers);
  }
}