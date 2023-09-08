package hydra.core;

import java.io.Serializable;

/**
 * A set of (possibly recursive) 'let' bindings
 */
public class Let<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Let");
  
  public final java.util.Map<hydra.core.Name, hydra.core.Term<A>> bindings;
  
  public final hydra.core.Term<A> environment;
  
  public Let (java.util.Map<hydra.core.Name, hydra.core.Term<A>> bindings, hydra.core.Term<A> environment) {
    this.bindings = bindings;
    this.environment = environment;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Let)) {
      return false;
    }
    Let o = (Let) (other);
    return bindings.equals(o.bindings) && environment.equals(o.environment);
  }
  
  @Override
  public int hashCode() {
    return 2 * bindings.hashCode() + 3 * environment.hashCode();
  }
  
  public Let withBindings(java.util.Map<hydra.core.Name, hydra.core.Term<A>> bindings) {
    return new Let(bindings, environment);
  }
  
  public Let withEnvironment(hydra.core.Term<A> environment) {
    return new Let(bindings, environment);
  }
}