package hydra.core;

import java.io.Serializable;

/**
 * A tuple elimination; a projection from an integer-indexed product
 */
public class TupleProjection implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.TupleProjection");
  
  /**
   * The arity of the tuple
   */
  public final Integer arity;
  
  /**
   * The 0-indexed offset from the beginning of the tuple
   */
  public final Integer index;
  
  public TupleProjection (Integer arity, Integer index) {
    this.arity = arity;
    this.index = index;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TupleProjection)) {
      return false;
    }
    TupleProjection o = (TupleProjection) (other);
    return arity.equals(o.arity) && index.equals(o.index);
  }
  
  @Override
  public int hashCode() {
    return 2 * arity.hashCode() + 3 * index.hashCode();
  }
  
  public TupleProjection withArity(Integer arity) {
    return new TupleProjection(arity, index);
  }
  
  public TupleProjection withIndex(Integer index) {
    return new TupleProjection(arity, index);
  }
}