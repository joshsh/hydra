package hydra.query;

import java.io.Serializable;

/**
 * A range from min to max, inclusive
 */
public class Range implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/query.Range");
  
  public final Integer min;
  
  public final Integer max;
  
  public Range (Integer min, Integer max) {
    this.min = min;
    this.max = max;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Range)) {
      return false;
    }
    Range o = (Range) (other);
    return min.equals(o.min) && max.equals(o.max);
  }
  
  @Override
  public int hashCode() {
    return 2 * min.hashCode() + 3 * max.hashCode();
  }
  
  public Range withMin(Integer min) {
    return new Range(min, max);
  }
  
  public Range withMax(Integer max) {
    return new Range(min, max);
  }
}