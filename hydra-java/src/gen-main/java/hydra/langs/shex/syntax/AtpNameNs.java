// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class AtpNameNs implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.AtpNameNs");
  
  public final hydra.util.Opt<hydra.langs.shex.syntax.PnPrefix> value;
  
  public AtpNameNs (hydra.util.Opt<hydra.langs.shex.syntax.PnPrefix> value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AtpNameNs)) {
      return false;
    }
    AtpNameNs o = (AtpNameNs) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}