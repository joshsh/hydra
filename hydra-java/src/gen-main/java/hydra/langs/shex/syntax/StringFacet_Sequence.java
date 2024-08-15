// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StringFacet_Sequence implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringFacet.Sequence");
  
  public static final hydra.core.Name FIELD_NAME_STRING_LENGTH = new hydra.core.Name("stringLength");
  
  public static final hydra.core.Name FIELD_NAME_INTEGER = new hydra.core.Name("integer");
  
  public final hydra.langs.shex.syntax.StringLength stringLength;
  
  public final hydra.langs.shex.syntax.Integer_ integer;
  
  public StringFacet_Sequence (hydra.langs.shex.syntax.StringLength stringLength, hydra.langs.shex.syntax.Integer_ integer) {
    java.util.Objects.requireNonNull((stringLength));
    java.util.Objects.requireNonNull((integer));
    this.stringLength = stringLength;
    this.integer = integer;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringFacet_Sequence)) {
      return false;
    }
    StringFacet_Sequence o = (StringFacet_Sequence) (other);
    return stringLength.equals(o.stringLength) && integer.equals(o.integer);
  }
  
  @Override
  public int hashCode() {
    return 2 * stringLength.hashCode() + 3 * integer.hashCode();
  }
  
  public StringFacet_Sequence withStringLength(hydra.langs.shex.syntax.StringLength stringLength) {
    java.util.Objects.requireNonNull((stringLength));
    return new StringFacet_Sequence(stringLength, integer);
  }
  
  public StringFacet_Sequence withInteger(hydra.langs.shex.syntax.Integer_ integer) {
    java.util.Objects.requireNonNull((integer));
    return new StringFacet_Sequence(stringLength, integer);
  }
}