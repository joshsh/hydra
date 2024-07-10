// Note: this is an automatically generated file. Do not edit.

package hydra.core;

import java.io.Serializable;

/**
 * A case statement for matching optional terms
 */
public class OptionalCases<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.OptionalCases");
  
  /**
   * A term provided if the optional value is nothing
   */
  public final hydra.core.Term<A> nothing;
  
  /**
   * A function which is applied if the optional value is non-nothing
   */
  public final hydra.core.Term<A> just;
  
  public OptionalCases (hydra.core.Term<A> nothing, hydra.core.Term<A> just) {
    if (nothing == null) {
      throw new IllegalArgumentException("null value for 'nothing' argument");
    }
    if (just == null) {
      throw new IllegalArgumentException("null value for 'just' argument");
    }
    this.nothing = nothing;
    this.just = just;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof OptionalCases)) {
      return false;
    }
    OptionalCases o = (OptionalCases) (other);
    return nothing.equals(o.nothing) && just.equals(o.just);
  }
  
  @Override
  public int hashCode() {
    return 2 * nothing.hashCode() + 3 * just.hashCode();
  }
  
  public OptionalCases withNothing(hydra.core.Term<A> nothing) {
    if (nothing == null) {
      throw new IllegalArgumentException("null value for 'nothing' argument");
    }
    return new OptionalCases(nothing, just);
  }
  
  public OptionalCases withJust(hydra.core.Term<A> just) {
    if (just == null) {
      throw new IllegalArgumentException("null value for 'just' argument");
    }
    return new OptionalCases(nothing, just);
  }
}