package hydra.compute;

import java.io.Serializable;

/**
 * The result of evaluating a Flow
 */
public class FlowState<S, X> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/compute.FlowState");
  
  public final java.util.Optional<X> value;
  
  public final S state;
  
  public final hydra.compute.Trace trace;
  
  public FlowState (java.util.Optional<X> value, S state, hydra.compute.Trace trace) {
    this.value = value;
    this.state = state;
    this.trace = trace;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FlowState)) {
      return false;
    }
    FlowState o = (FlowState) (other);
    return value.equals(o.value) && state.equals(o.state) && trace.equals(o.trace);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode() + 3 * state.hashCode() + 5 * trace.hashCode();
  }
  
  public FlowState withValue(java.util.Optional<X> value) {
    return new FlowState(value, state, trace);
  }
  
  public FlowState withState(S state) {
    return new FlowState(value, state, trace);
  }
  
  public FlowState withTrace(hydra.compute.Trace trace) {
    return new FlowState(value, state, trace);
  }
}