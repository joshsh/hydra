package hydra.langs.java.syntax;

import java.io.Serializable;

public class SwitchBlock implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.SwitchBlock");
  
  public final java.util.List<hydra.langs.java.syntax.SwitchBlock_Pair> value;
  
  public SwitchBlock (java.util.List<hydra.langs.java.syntax.SwitchBlock_Pair> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SwitchBlock)) {
      return false;
    }
    SwitchBlock o = (SwitchBlock) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}