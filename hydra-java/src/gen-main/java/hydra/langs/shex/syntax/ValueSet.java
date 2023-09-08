package hydra.langs.shex.syntax;

import java.io.Serializable;

public class ValueSet implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ValueSet");
  
  public final java.util.List<hydra.langs.shex.syntax.ValueSetValue> value;
  
  public ValueSet (java.util.List<hydra.langs.shex.syntax.ValueSetValue> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ValueSet)) {
      return false;
    }
    ValueSet o = (ValueSet) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}