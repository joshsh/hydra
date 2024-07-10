// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.gremlin;

import java.io.Serializable;

public class WhereWithPredicateArgs implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/gremlin.WhereWithPredicateArgs");
  
  public final java.util.Optional<hydra.langs.tinkerpop.gremlin.StringArgument> leftArg;
  
  public final hydra.langs.tinkerpop.gremlin.TraversalPredicate predicate;
  
  public WhereWithPredicateArgs (java.util.Optional<hydra.langs.tinkerpop.gremlin.StringArgument> leftArg, hydra.langs.tinkerpop.gremlin.TraversalPredicate predicate) {
    if (leftArg == null) {
      throw new IllegalArgumentException("null value for 'leftArg' argument");
    }
    if (predicate == null) {
      throw new IllegalArgumentException("null value for 'predicate' argument");
    }
    this.leftArg = leftArg;
    this.predicate = predicate;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof WhereWithPredicateArgs)) {
      return false;
    }
    WhereWithPredicateArgs o = (WhereWithPredicateArgs) (other);
    return leftArg.equals(o.leftArg) && predicate.equals(o.predicate);
  }
  
  @Override
  public int hashCode() {
    return 2 * leftArg.hashCode() + 3 * predicate.hashCode();
  }
  
  public WhereWithPredicateArgs withLeftArg(java.util.Optional<hydra.langs.tinkerpop.gremlin.StringArgument> leftArg) {
    if (leftArg == null) {
      throw new IllegalArgumentException("null value for 'leftArg' argument");
    }
    return new WhereWithPredicateArgs(leftArg, predicate);
  }
  
  public WhereWithPredicateArgs withPredicate(hydra.langs.tinkerpop.gremlin.TraversalPredicate predicate) {
    if (predicate == null) {
      throw new IllegalArgumentException("null value for 'predicate' argument");
    }
    return new WhereWithPredicateArgs(leftArg, predicate);
  }
}