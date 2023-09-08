package hydra.core;

import java.io.Serializable;

/**
 * A term which applies a function to an argument
 */
public class Application<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Application");
  
  /**
   * The left-hand side of the application
   */
  public final hydra.core.Term<A> function;
  
  /**
   * The right-hand side of the application
   */
  public final hydra.core.Term<A> argument;
  
  public Application (hydra.core.Term<A> function, hydra.core.Term<A> argument) {
    this.function = function;
    this.argument = argument;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Application)) {
      return false;
    }
    Application o = (Application) (other);
    return function.equals(o.function) && argument.equals(o.argument);
  }
  
  @Override
  public int hashCode() {
    return 2 * function.hashCode() + 3 * argument.hashCode();
  }
  
  public Application withFunction(hydra.core.Term<A> function) {
    return new Application(function, argument);
  }
  
  public Application withArgument(hydra.core.Term<A> argument) {
    return new Application(function, argument);
  }
}