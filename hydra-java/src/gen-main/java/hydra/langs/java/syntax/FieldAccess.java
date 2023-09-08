package hydra.langs.java.syntax;

import java.io.Serializable;

public class FieldAccess implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.FieldAccess");
  
  public final hydra.langs.java.syntax.FieldAccess_Qualifier qualifier;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public FieldAccess (hydra.langs.java.syntax.FieldAccess_Qualifier qualifier, hydra.langs.java.syntax.Identifier identifier) {
    this.qualifier = qualifier;
    this.identifier = identifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldAccess)) {
      return false;
    }
    FieldAccess o = (FieldAccess) (other);
    return qualifier.equals(o.qualifier) && identifier.equals(o.identifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * qualifier.hashCode() + 3 * identifier.hashCode();
  }
  
  public FieldAccess withQualifier(hydra.langs.java.syntax.FieldAccess_Qualifier qualifier) {
    return new FieldAccess(qualifier, identifier);
  }
  
  public FieldAccess withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new FieldAccess(qualifier, identifier);
  }
}