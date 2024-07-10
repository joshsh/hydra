// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class ClassOrInterfaceTypeToInstantiate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ClassOrInterfaceTypeToInstantiate");
  
  public final java.util.List<hydra.langs.java.syntax.AnnotatedIdentifier> identifiers;
  
  public final java.util.Optional<hydra.langs.java.syntax.TypeArgumentsOrDiamond> typeArguments;
  
  public ClassOrInterfaceTypeToInstantiate (java.util.List<hydra.langs.java.syntax.AnnotatedIdentifier> identifiers, java.util.Optional<hydra.langs.java.syntax.TypeArgumentsOrDiamond> typeArguments) {
    if (identifiers == null) {
      throw new IllegalArgumentException("null value for 'identifiers' argument");
    }
    if (typeArguments == null) {
      throw new IllegalArgumentException("null value for 'typeArguments' argument");
    }
    this.identifiers = identifiers;
    this.typeArguments = typeArguments;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ClassOrInterfaceTypeToInstantiate)) {
      return false;
    }
    ClassOrInterfaceTypeToInstantiate o = (ClassOrInterfaceTypeToInstantiate) (other);
    return identifiers.equals(o.identifiers) && typeArguments.equals(o.typeArguments);
  }
  
  @Override
  public int hashCode() {
    return 2 * identifiers.hashCode() + 3 * typeArguments.hashCode();
  }
  
  public ClassOrInterfaceTypeToInstantiate withIdentifiers(java.util.List<hydra.langs.java.syntax.AnnotatedIdentifier> identifiers) {
    if (identifiers == null) {
      throw new IllegalArgumentException("null value for 'identifiers' argument");
    }
    return new ClassOrInterfaceTypeToInstantiate(identifiers, typeArguments);
  }
  
  public ClassOrInterfaceTypeToInstantiate withTypeArguments(java.util.Optional<hydra.langs.java.syntax.TypeArgumentsOrDiamond> typeArguments) {
    if (typeArguments == null) {
      throw new IllegalArgumentException("null value for 'typeArguments' argument");
    }
    return new ClassOrInterfaceTypeToInstantiate(identifiers, typeArguments);
  }
}