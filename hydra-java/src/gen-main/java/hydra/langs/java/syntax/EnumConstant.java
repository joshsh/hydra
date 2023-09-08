package hydra.langs.java.syntax;

import java.io.Serializable;

public class EnumConstant implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.EnumConstant");
  
  public final java.util.List<hydra.langs.java.syntax.EnumConstantModifier> modifiers;
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public final java.util.List<java.util.List<hydra.langs.java.syntax.Expression>> arguments;
  
  public final java.util.Optional<hydra.langs.java.syntax.ClassBody> body;
  
  public EnumConstant (java.util.List<hydra.langs.java.syntax.EnumConstantModifier> modifiers, hydra.langs.java.syntax.Identifier identifier, java.util.List<java.util.List<hydra.langs.java.syntax.Expression>> arguments, java.util.Optional<hydra.langs.java.syntax.ClassBody> body) {
    this.modifiers = modifiers;
    this.identifier = identifier;
    this.arguments = arguments;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumConstant)) {
      return false;
    }
    EnumConstant o = (EnumConstant) (other);
    return modifiers.equals(o.modifiers) && identifier.equals(o.identifier) && arguments.equals(o.arguments) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * modifiers.hashCode() + 3 * identifier.hashCode() + 5 * arguments.hashCode() + 7 * body.hashCode();
  }
  
  public EnumConstant withModifiers(java.util.List<hydra.langs.java.syntax.EnumConstantModifier> modifiers) {
    return new EnumConstant(modifiers, identifier, arguments, body);
  }
  
  public EnumConstant withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    return new EnumConstant(modifiers, identifier, arguments, body);
  }
  
  public EnumConstant withArguments(java.util.List<java.util.List<hydra.langs.java.syntax.Expression>> arguments) {
    return new EnumConstant(modifiers, identifier, arguments, body);
  }
  
  public EnumConstant withBody(java.util.Optional<hydra.langs.java.syntax.ClassBody> body) {
    return new EnumConstant(modifiers, identifier, arguments, body);
  }
}