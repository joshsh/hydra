package hydra.langs.java.syntax;

import java.io.Serializable;

public class UnqualifiedClassInstanceCreationExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.UnqualifiedClassInstanceCreationExpression");
  
  public final java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments;
  
  public final hydra.langs.java.syntax.ClassOrInterfaceTypeToInstantiate classOrInterface;
  
  public final java.util.List<hydra.langs.java.syntax.Expression> arguments;
  
  public final java.util.Optional<hydra.langs.java.syntax.ClassBody> body;
  
  public UnqualifiedClassInstanceCreationExpression (java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments, hydra.langs.java.syntax.ClassOrInterfaceTypeToInstantiate classOrInterface, java.util.List<hydra.langs.java.syntax.Expression> arguments, java.util.Optional<hydra.langs.java.syntax.ClassBody> body) {
    this.typeArguments = typeArguments;
    this.classOrInterface = classOrInterface;
    this.arguments = arguments;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnqualifiedClassInstanceCreationExpression)) {
      return false;
    }
    UnqualifiedClassInstanceCreationExpression o = (UnqualifiedClassInstanceCreationExpression) (other);
    return typeArguments.equals(o.typeArguments) && classOrInterface.equals(o.classOrInterface) && arguments.equals(o.arguments) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeArguments.hashCode() + 3 * classOrInterface.hashCode() + 5 * arguments.hashCode() + 7 * body.hashCode();
  }
  
  public UnqualifiedClassInstanceCreationExpression withTypeArguments(java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments) {
    return new UnqualifiedClassInstanceCreationExpression(typeArguments, classOrInterface, arguments, body);
  }
  
  public UnqualifiedClassInstanceCreationExpression withClassOrInterface(hydra.langs.java.syntax.ClassOrInterfaceTypeToInstantiate classOrInterface) {
    return new UnqualifiedClassInstanceCreationExpression(typeArguments, classOrInterface, arguments, body);
  }
  
  public UnqualifiedClassInstanceCreationExpression withArguments(java.util.List<hydra.langs.java.syntax.Expression> arguments) {
    return new UnqualifiedClassInstanceCreationExpression(typeArguments, classOrInterface, arguments, body);
  }
  
  public UnqualifiedClassInstanceCreationExpression withBody(java.util.Optional<hydra.langs.java.syntax.ClassBody> body) {
    return new UnqualifiedClassInstanceCreationExpression(typeArguments, classOrInterface, arguments, body);
  }
}