package hydra.langs.shex.syntax;

import java.io.Serializable;

public class PnLocalEsc implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.PnLocalEsc");
  
  public final String value;
  
  public PnLocalEsc (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PnLocalEsc)) {
      return false;
    }
    PnLocalEsc o = (PnLocalEsc) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}