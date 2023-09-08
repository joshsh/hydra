package hydra.langs.shex.syntax;

import java.io.Serializable;

public class BaseDecl implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.BaseDecl");
  
  public final hydra.langs.shex.syntax.IriRef value;
  
  public BaseDecl (hydra.langs.shex.syntax.IriRef value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BaseDecl)) {
      return false;
    }
    BaseDecl o = (BaseDecl) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}