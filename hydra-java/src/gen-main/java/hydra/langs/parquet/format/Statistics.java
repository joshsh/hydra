package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Statistics per row group and per page. All fields are optional.
 */
public class Statistics implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.Statistics");
  
  public final java.util.Optional<java.math.BigInteger> nullCount;
  
  public final java.util.Optional<java.math.BigInteger> distinctCount;
  
  public final java.util.Optional<String> maxValue;
  
  public final java.util.Optional<String> minValue;
  
  public Statistics (java.util.Optional<java.math.BigInteger> nullCount, java.util.Optional<java.math.BigInteger> distinctCount, java.util.Optional<String> maxValue, java.util.Optional<String> minValue) {
    this.nullCount = nullCount;
    this.distinctCount = distinctCount;
    this.maxValue = maxValue;
    this.minValue = minValue;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Statistics)) {
      return false;
    }
    Statistics o = (Statistics) (other);
    return nullCount.equals(o.nullCount) && distinctCount.equals(o.distinctCount) && maxValue.equals(o.maxValue) && minValue.equals(o.minValue);
  }
  
  @Override
  public int hashCode() {
    return 2 * nullCount.hashCode() + 3 * distinctCount.hashCode() + 5 * maxValue.hashCode() + 7 * minValue.hashCode();
  }
  
  public Statistics withNullCount(java.util.Optional<java.math.BigInteger> nullCount) {
    return new Statistics(nullCount, distinctCount, maxValue, minValue);
  }
  
  public Statistics withDistinctCount(java.util.Optional<java.math.BigInteger> distinctCount) {
    return new Statistics(nullCount, distinctCount, maxValue, minValue);
  }
  
  public Statistics withMaxValue(java.util.Optional<String> maxValue) {
    return new Statistics(nullCount, distinctCount, maxValue, minValue);
  }
  
  public Statistics withMinValue(java.util.Optional<String> minValue) {
    return new Statistics(nullCount, distinctCount, maxValue, minValue);
  }
}