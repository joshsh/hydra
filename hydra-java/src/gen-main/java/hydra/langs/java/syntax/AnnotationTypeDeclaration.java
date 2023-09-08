package hydra.langs.java.syntax;

import java.io.Serializable;

public class AnnotationTypeDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.AnnotationTypeDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.InterfaceModifier> modifiers;
  
  public final hydra.langs.java.syntax.TypeIdentifier identifier;
  
  public final hydra.langs.java.syntax.AnnotationTypeBody body;
  
  public AnnotationTypeDeclaration (java.util.List<hydra.langs.java.syntax.InterfaceModifier> modifiers, hydra.langs.java.syntax.TypeIdentifier identifier, hydra.langs.java.syntax.AnnotationTypeBody body) {
    this.modifiers = modifiers;
    this.identifier = identifier;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnnotationTypeDeclaration)) {
      return false;
    }
    AnnotationTypeDeclaration o = (AnnotationTypeDeclaration) (other);
    return modifiers.equals(o.modifiers) && identifier.equals(o.identifier) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * identifier.hashCode() + 5 * body.hashCode();
  }
  
  public AnnotationTypeDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.InterfaceModifier> modifiers) {
    return new AnnotationTypeDeclaration(modifiers, identifier, body);
  }
  
  public AnnotationTypeDeclaration withIdentifier(hydra.langs.java.syntax.TypeIdentifier identifier) {
    return new AnnotationTypeDeclaration(modifiers, identifier, body);
  }
  
  public AnnotationTypeDeclaration withBody(hydra.langs.java.syntax.AnnotationTypeBody body) {
    return new AnnotationTypeDeclaration(modifiers, identifier, body);
  }
}