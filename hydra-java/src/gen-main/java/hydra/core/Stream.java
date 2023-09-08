package hydra.core;

import java.io.Serializable;

/**
 * An infinite stream of terms
 */
public class Stream<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Stream");
  
  public final hydra.core.Term<A> first;
  
  public final hydra.core.Stream<A> rest;
  
  public Stream (hydra.core.Term<A> first, hydra.core.Stream<A> rest) {
    this.first = first;
    this.rest = rest;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Stream)) {
      return false;
    }
    Stream o = (Stream) (other);
    return first.equals(o.first) && rest.equals(o.rest);
  }
  
  @Override
  public int hashCode() {
    return 2 * first.hashCode() + 3 * rest.hashCode();
  }
  
  public Stream withFirst(hydra.core.Term<A> first) {
    return new Stream(first, rest);
  }
  
  public Stream withRest(hydra.core.Stream<A> rest) {
    return new Stream(first, rest);
  }
}