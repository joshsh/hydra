package hydra.langs.java.syntax;

import java.io.Serializable;

public class InterfaceMethodDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.InterfaceMethodDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.InterfaceMethodModifier> modifiers;
  
  public final hydra.langs.java.syntax.MethodHeader header;
  
  public final hydra.langs.java.syntax.MethodBody body;
  
  public InterfaceMethodDeclaration (java.util.List<hydra.langs.java.syntax.InterfaceMethodModifier> modifiers, hydra.langs.java.syntax.MethodHeader header, hydra.langs.java.syntax.MethodBody body) {
    this.modifiers = modifiers;
    this.header = header;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InterfaceMethodDeclaration)) {
      return false;
    }
    InterfaceMethodDeclaration o = (InterfaceMethodDeclaration) (other);
    return modifiers.equals(o.modifiers) && header.equals(o.header) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * header.hashCode() + 5 * body.hashCode();
  }
  
  public InterfaceMethodDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.InterfaceMethodModifier> modifiers) {
    return new InterfaceMethodDeclaration(modifiers, header, body);
  }
  
  public InterfaceMethodDeclaration withHeader(hydra.langs.java.syntax.MethodHeader header) {
    return new InterfaceMethodDeclaration(modifiers, header, body);
  }
  
  public InterfaceMethodDeclaration withBody(hydra.langs.java.syntax.MethodBody body) {
    return new InterfaceMethodDeclaration(modifiers, header, body);
  }
}