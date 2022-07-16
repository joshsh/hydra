package hydra.ext.java.syntax;

public class TypeName {
  public final TypeIdentifier identifier;
  
  public final java.util.Optional<PackageOrTypeName> qualifier;
  
  public TypeName (TypeIdentifier identifier, java.util.Optional<PackageOrTypeName> qualifier) {
    this.identifier = identifier;
    this.qualifier = qualifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeName)) {
      return false;
    }
    TypeName o = (TypeName) (other);
    return identifier.equals(o.identifier) && qualifier.equals(o.qualifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * identifier.hashCode() + 3 * qualifier.hashCode();
  }
  
  public TypeName withIdentifier(TypeIdentifier identifier) {
    return new TypeName(identifier, qualifier);
  }
  
  public TypeName withQualifier(java.util.Optional<PackageOrTypeName> qualifier) {
    return new TypeName(identifier, qualifier);
  }
}