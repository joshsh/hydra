package hydra.langs.java.syntax;

import java.io.Serializable;

public class ExplicitConstructorInvocation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ExplicitConstructorInvocation");
  
  public final java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments;
  
  public final java.util.List<hydra.langs.java.syntax.Expression> arguments;
  
  public final hydra.langs.java.syntax.ExplicitConstructorInvocation_Variant variant;
  
  public ExplicitConstructorInvocation (java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments, java.util.List<hydra.langs.java.syntax.Expression> arguments, hydra.langs.java.syntax.ExplicitConstructorInvocation_Variant variant) {
    this.typeArguments = typeArguments;
    this.arguments = arguments;
    this.variant = variant;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExplicitConstructorInvocation)) {
      return false;
    }
    ExplicitConstructorInvocation o = (ExplicitConstructorInvocation) (other);
    return typeArguments.equals(o.typeArguments) && arguments.equals(o.arguments) && variant.equals(o.variant);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeArguments.hashCode() + 3 * arguments.hashCode() + 5 * variant.hashCode();
  }
  
  public ExplicitConstructorInvocation withTypeArguments(java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments) {
    return new ExplicitConstructorInvocation(typeArguments, arguments, variant);
  }
  
  public ExplicitConstructorInvocation withArguments(java.util.List<hydra.langs.java.syntax.Expression> arguments) {
    return new ExplicitConstructorInvocation(typeArguments, arguments, variant);
  }
  
  public ExplicitConstructorInvocation withVariant(hydra.langs.java.syntax.ExplicitConstructorInvocation_Variant variant) {
    return new ExplicitConstructorInvocation(typeArguments, arguments, variant);
  }
}