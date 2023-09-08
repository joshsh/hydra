package hydra.mantle;

import java.io.Serializable;

/**
 * A type expression together with free type variables occurring in the expression
 */
public class TypeScheme<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/mantle.TypeScheme");
  
  public final java.util.List<hydra.core.Name> variables;
  
  public final hydra.core.Type<A> type;
  
  public TypeScheme (java.util.List<hydra.core.Name> variables, hydra.core.Type<A> type) {
    this.variables = variables;
    this.type = type;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeScheme)) {
      return false;
    }
    TypeScheme o = (TypeScheme) (other);
    return variables.equals(o.variables) && type.equals(o.type);
  }
  
  @Override
  public int hashCode() {
    return 2 * variables.hashCode() + 3 * type.hashCode();
  }
  
  public TypeScheme withVariables(java.util.List<hydra.core.Name> variables) {
    return new TypeScheme(variables, type);
  }
  
  public TypeScheme withType(hydra.core.Type<A> type) {
    return new TypeScheme(variables, type);
  }
}