package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class Directive implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.Directive");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Arguments> arguments;
  
  public Directive (hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.Arguments> arguments) {
    this.name = name;
    this.arguments = arguments;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Directive)) {
      return false;
    }
    Directive o = (Directive) (other);
    return name.equals(o.name) && arguments.equals(o.arguments);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * arguments.hashCode();
  }
  
  public Directive withName(hydra.langs.graphql.syntax.Name name) {
    return new Directive(name, arguments);
  }
  
  public Directive withArguments(java.util.Optional<hydra.langs.graphql.syntax.Arguments> arguments) {
    return new Directive(name, arguments);
  }
}