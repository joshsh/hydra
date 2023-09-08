package hydra.langs.java.syntax;

import java.io.Serializable;

public class MethodDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MethodDeclaration");
  
  /**
   * Note: simple methods cannot have annotations
   */
  public final java.util.List<hydra.langs.java.syntax.Annotation> annotations;
  
  public final java.util.List<hydra.langs.java.syntax.MethodModifier> modifiers;
  
  public final hydra.langs.java.syntax.MethodHeader header;
  
  public final hydra.langs.java.syntax.MethodBody body;
  
  public MethodDeclaration (java.util.List<hydra.langs.java.syntax.Annotation> annotations, java.util.List<hydra.langs.java.syntax.MethodModifier> modifiers, hydra.langs.java.syntax.MethodHeader header, hydra.langs.java.syntax.MethodBody body) {
    this.annotations = annotations;
    this.modifiers = modifiers;
    this.header = header;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodDeclaration)) {
      return false;
    }
    MethodDeclaration o = (MethodDeclaration) (other);
    return annotations.equals(o.annotations) && modifiers.equals(o.modifiers) && header.equals(o.header) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * modifiers.hashCode() + 5 * header.hashCode() + 7 * body.hashCode();
  }
  
  public MethodDeclaration withAnnotations(java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    return new MethodDeclaration(annotations, modifiers, header, body);
  }
  
  public MethodDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.MethodModifier> modifiers) {
    return new MethodDeclaration(annotations, modifiers, header, body);
  }
  
  public MethodDeclaration withHeader(hydra.langs.java.syntax.MethodHeader header) {
    return new MethodDeclaration(annotations, modifiers, header, body);
  }
  
  public MethodDeclaration withBody(hydra.langs.java.syntax.MethodBody body) {
    return new MethodDeclaration(annotations, modifiers, header, body);
  }
}