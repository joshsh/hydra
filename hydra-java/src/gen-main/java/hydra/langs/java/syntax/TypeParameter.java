// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class TypeParameter implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TypeParameter");
  
  public final java.util.List<hydra.langs.java.syntax.TypeParameterModifier> modifiers;
  
  public final hydra.langs.java.syntax.TypeIdentifier identifier;
  
  public final java.util.Optional<hydra.langs.java.syntax.TypeBound> bound;
  
  public TypeParameter (java.util.List<hydra.langs.java.syntax.TypeParameterModifier> modifiers, hydra.langs.java.syntax.TypeIdentifier identifier, java.util.Optional<hydra.langs.java.syntax.TypeBound> bound) {
    if (modifiers == null) {
      throw new IllegalArgumentException("null value for 'modifiers' argument");
    }
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    if (bound == null) {
      throw new IllegalArgumentException("null value for 'bound' argument");
    }
    this.modifiers = modifiers;
    this.identifier = identifier;
    this.bound = bound;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeParameter)) {
      return false;
    }
    TypeParameter o = (TypeParameter) (other);
    return modifiers.equals(o.modifiers) && identifier.equals(o.identifier) && bound.equals(o.bound);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * identifier.hashCode() + 5 * bound.hashCode();
  }
  
  public TypeParameter withModifiers(java.util.List<hydra.langs.java.syntax.TypeParameterModifier> modifiers) {
    if (modifiers == null) {
      throw new IllegalArgumentException("null value for 'modifiers' argument");
    }
    return new TypeParameter(modifiers, identifier, bound);
  }
  
  public TypeParameter withIdentifier(hydra.langs.java.syntax.TypeIdentifier identifier) {
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    return new TypeParameter(modifiers, identifier, bound);
  }
  
  public TypeParameter withBound(java.util.Optional<hydra.langs.java.syntax.TypeBound> bound) {
    if (bound == null) {
      throw new IllegalArgumentException("null value for 'bound' argument");
    }
    return new TypeParameter(modifiers, identifier, bound);
  }
}