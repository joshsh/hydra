package hydra.langs.shex.syntax;

import java.io.Serializable;

public class ExtraPropertySet implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ExtraPropertySet");
  
  public final java.util.List<hydra.langs.shex.syntax.Predicate> value;
  
  public ExtraPropertySet (java.util.List<hydra.langs.shex.syntax.Predicate> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExtraPropertySet)) {
      return false;
    }
    ExtraPropertySet o = (ExtraPropertySet) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}