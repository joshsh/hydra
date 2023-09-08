package hydra.langs.java.syntax;

import java.io.Serializable;

public class ConstructorDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ConstructorDeclaration");
  
  public final java.util.List<hydra.langs.java.syntax.ConstructorModifier> modifiers;
  
  public final hydra.langs.java.syntax.ConstructorDeclarator constructor;
  
  public final java.util.Optional<hydra.langs.java.syntax.Throws> throws_;
  
  public final hydra.langs.java.syntax.ConstructorBody body;
  
  public ConstructorDeclaration (java.util.List<hydra.langs.java.syntax.ConstructorModifier> modifiers, hydra.langs.java.syntax.ConstructorDeclarator constructor, java.util.Optional<hydra.langs.java.syntax.Throws> throws_, hydra.langs.java.syntax.ConstructorBody body) {
    this.modifiers = modifiers;
    this.constructor = constructor;
    this.throws_ = throws_;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ConstructorDeclaration)) {
      return false;
    }
    ConstructorDeclaration o = (ConstructorDeclaration) (other);
    return modifiers.equals(o.modifiers) && constructor.equals(o.constructor) && throws_.equals(o.throws_) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * constructor.hashCode() + 5 * throws_.hashCode() + 7 * body.hashCode();
  }
  
  public ConstructorDeclaration withModifiers(java.util.List<hydra.langs.java.syntax.ConstructorModifier> modifiers) {
    return new ConstructorDeclaration(modifiers, constructor, throws_, body);
  }
  
  public ConstructorDeclaration withConstructor(hydra.langs.java.syntax.ConstructorDeclarator constructor) {
    return new ConstructorDeclaration(modifiers, constructor, throws_, body);
  }
  
  public ConstructorDeclaration withThrows(java.util.Optional<hydra.langs.java.syntax.Throws> throws_) {
    return new ConstructorDeclaration(modifiers, constructor, throws_, body);
  }
  
  public ConstructorDeclaration withBody(hydra.langs.java.syntax.ConstructorBody body) {
    return new ConstructorDeclaration(modifiers, constructor, throws_, body);
  }
}