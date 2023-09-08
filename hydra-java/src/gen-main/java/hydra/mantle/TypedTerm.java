package hydra.mantle;

import java.io.Serializable;

/**
 * A type together with an instance of the type
 */
public class TypedTerm<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/mantle.TypedTerm");
  
  public final hydra.core.Type<A> type;
  
  public final hydra.core.Term<A> term;
  
  public TypedTerm (hydra.core.Type<A> type, hydra.core.Term<A> term) {
    this.type = type;
    this.term = term;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypedTerm)) {
      return false;
    }
    TypedTerm o = (TypedTerm) (other);
    return type.equals(o.type) && term.equals(o.term);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * term.hashCode();
  }
  
  public TypedTerm withType(hydra.core.Type<A> type) {
    return new TypedTerm(type, term);
  }
  
  public TypedTerm withTerm(hydra.core.Term<A> term) {
    return new TypedTerm(type, term);
  }
}