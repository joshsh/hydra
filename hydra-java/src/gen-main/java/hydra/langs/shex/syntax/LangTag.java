package hydra.langs.shex.syntax;

import java.io.Serializable;

public class LangTag implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.LangTag");
  
  public final String value;
  
  public LangTag (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LangTag)) {
      return false;
    }
    LangTag o = (LangTag) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}