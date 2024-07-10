// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class NormalInterfaceDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.NormalInterfaceDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.InterfaceModifier> modifiers;
  
  public final hydra.langs.java.syntax.TypeIdentifier identifier;
  
  public final java.util.List<hydra.langs.java.syntax.TypeParameter> parameters;
  
  public final java.util.List<hydra.langs.java.syntax.InterfaceType> extends_;
  
  public final hydra.langs.java.syntax.InterfaceBody body;
  
  public NormalInterfaceDeclaration (java.util.List<hydra.langs.java.syntax.InterfaceModifier> modifiers, hydra.langs.java.syntax.TypeIdentifier identifier, java.util.List<hydra.langs.java.syntax.TypeParameter> parameters, java.util.List<hydra.langs.java.syntax.InterfaceType> extends_, hydra.langs.java.syntax.InterfaceBody body) {
    if (modifiers == null) {
      throw new IllegalArgumentException("null value for 'modifiers' argument");
    }
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    if (parameters == null) {
      throw new IllegalArgumentException("null value for 'parameters' argument");
    }
    if (extends_ == null) {
      throw new IllegalArgumentException("null value for 'extends' argument");
    }
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
    this.modifiers = modifiers;
    this.identifier = identifier;
    this.parameters = parameters;
    this.extends_ = extends_;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NormalInterfaceDeclaration)) {
      return false;
    }
    NormalInterfaceDeclaration o = (NormalInterfaceDeclaration) (other);
    return modifiers.equals(o.modifiers) && identifier.equals(o.identifier) && parameters.equals(o.parameters) && extends_.equals(o.extends_) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * identifier.hashCode() + 5 * parameters.hashCode() + 7 * extends_.hashCode() + 11 * body.hashCode();
  }
  
  public NormalInterfaceDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.InterfaceModifier> modifiers) {
    if (modifiers == null) {
      throw new IllegalArgumentException("null value for 'modifiers' argument");
    }
    return new NormalInterfaceDeclaration(modifiers, identifier, parameters, extends_, body);
  }
  
  public NormalInterfaceDeclaration withIdentifier(hydra.langs.java.syntax.TypeIdentifier identifier) {
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    return new NormalInterfaceDeclaration(modifiers, identifier, parameters, extends_, body);
  }
  
  public NormalInterfaceDeclaration withParameters(java.util.List<hydra.langs.java.syntax.TypeParameter> parameters) {
    if (parameters == null) {
      throw new IllegalArgumentException("null value for 'parameters' argument");
    }
    return new NormalInterfaceDeclaration(modifiers, identifier, parameters, extends_, body);
  }
  
  public NormalInterfaceDeclaration withExtends(java.util.List<hydra.langs.java.syntax.InterfaceType> extends_) {
    if (extends_ == null) {
      throw new IllegalArgumentException("null value for 'extends' argument");
    }
    return new NormalInterfaceDeclaration(modifiers, identifier, parameters, extends_, body);
  }
  
  public NormalInterfaceDeclaration withBody(hydra.langs.java.syntax.InterfaceBody body) {
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
    return new NormalInterfaceDeclaration(modifiers, identifier, parameters, extends_, body);
  }
}