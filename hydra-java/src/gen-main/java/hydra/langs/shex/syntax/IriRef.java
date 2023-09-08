package hydra.langs.shex.syntax;

import java.io.Serializable;

public class IriRef implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.IriRef");
  
  public final java.util.List<hydra.langs.shex.syntax.IriRef_Elmt> value;
  
  public IriRef (java.util.List<hydra.langs.shex.syntax.IriRef_Elmt> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IriRef)) {
      return false;
    }
    IriRef o = (IriRef) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}