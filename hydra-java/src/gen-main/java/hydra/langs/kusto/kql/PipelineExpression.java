// Note: this is an automatically generated file. Do not edit.

package hydra.langs.kusto.kql;

import java.io.Serializable;

public class PipelineExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/kusto/kql.PipelineExpression");
  
  public final java.util.List<hydra.langs.kusto.kql.TabularExpression> value;
  
  public PipelineExpression (java.util.List<hydra.langs.kusto.kql.TabularExpression> value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PipelineExpression)) {
      return false;
    }
    PipelineExpression o = (PipelineExpression) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}