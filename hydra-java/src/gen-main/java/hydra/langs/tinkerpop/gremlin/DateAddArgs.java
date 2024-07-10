// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.gremlin;

import java.io.Serializable;

public class DateAddArgs implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/gremlin.DateAddArgs");
  
  public final hydra.langs.tinkerpop.gremlin.TraversalDTArgument unit;
  
  public final hydra.langs.tinkerpop.gremlin.IntegerArgument duration;
  
  public DateAddArgs (hydra.langs.tinkerpop.gremlin.TraversalDTArgument unit, hydra.langs.tinkerpop.gremlin.IntegerArgument duration) {
    if (unit == null) {
      throw new IllegalArgumentException("null value for 'unit' argument");
    }
    if (duration == null) {
      throw new IllegalArgumentException("null value for 'duration' argument");
    }
    this.unit = unit;
    this.duration = duration;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DateAddArgs)) {
      return false;
    }
    DateAddArgs o = (DateAddArgs) (other);
    return unit.equals(o.unit) && duration.equals(o.duration);
  }
  
  @Override
  public int hashCode() {
    return 2 * unit.hashCode() + 3 * duration.hashCode();
  }
  
  public DateAddArgs withUnit(hydra.langs.tinkerpop.gremlin.TraversalDTArgument unit) {
    if (unit == null) {
      throw new IllegalArgumentException("null value for 'unit' argument");
    }
    return new DateAddArgs(unit, duration);
  }
  
  public DateAddArgs withDuration(hydra.langs.tinkerpop.gremlin.IntegerArgument duration) {
    if (duration == null) {
      throw new IllegalArgumentException("null value for 'duration' argument");
    }
    return new DateAddArgs(unit, duration);
  }
}