package hydra.langs.rdf.syntax;

import java.io.Serializable;

/**
 * A BCP47 language tag
 */
public class LanguageTag implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/rdf/syntax.LanguageTag");
  
  /**
   * A BCP47 language tag
   */
  public final String value;
  
  public LanguageTag (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LanguageTag)) {
      return false;
    }
    LanguageTag o = (LanguageTag) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}