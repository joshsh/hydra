// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class MethodReference_ReferenceType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MethodReference.ReferenceType");
  
  public final hydra.langs.java.syntax.ReferenceType referenceType;
  
  public final java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public MethodReference_ReferenceType (hydra.langs.java.syntax.ReferenceType referenceType, java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments, hydra.langs.java.syntax.Identifier identifier) {
    if (referenceType == null) {
      throw new IllegalArgumentException("null value for 'referenceType' argument");
    }
    if (typeArguments == null) {
      throw new IllegalArgumentException("null value for 'typeArguments' argument");
    }
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    this.referenceType = referenceType;
    this.typeArguments = typeArguments;
    this.identifier = identifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodReference_ReferenceType)) {
      return false;
    }
    MethodReference_ReferenceType o = (MethodReference_ReferenceType) (other);
    return referenceType.equals(o.referenceType) && typeArguments.equals(o.typeArguments) && identifier.equals(o.identifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * referenceType.hashCode() + 3 * typeArguments.hashCode() + 5 * identifier.hashCode();
  }
  
  public MethodReference_ReferenceType withReferenceType(hydra.langs.java.syntax.ReferenceType referenceType) {
    if (referenceType == null) {
      throw new IllegalArgumentException("null value for 'referenceType' argument");
    }
    return new MethodReference_ReferenceType(referenceType, typeArguments, identifier);
  }
  
  public MethodReference_ReferenceType withTypeArguments(java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments) {
    if (typeArguments == null) {
      throw new IllegalArgumentException("null value for 'typeArguments' argument");
    }
    return new MethodReference_ReferenceType(referenceType, typeArguments, identifier);
  }
  
  public MethodReference_ReferenceType withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    if (identifier == null) {
      throw new IllegalArgumentException("null value for 'identifier' argument");
    }
    return new MethodReference_ReferenceType(referenceType, typeArguments, identifier);
  }
}