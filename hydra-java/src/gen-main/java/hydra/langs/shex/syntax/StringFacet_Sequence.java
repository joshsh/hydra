// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StringFacet_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringFacet.Sequence");
  
  public final hydra.langs.shex.syntax.StringLength stringLength;
  
  public final hydra.langs.shex.syntax.Integer_ integer;
  
  public StringFacet_Sequence (hydra.langs.shex.syntax.StringLength stringLength, hydra.langs.shex.syntax.Integer_ integer) {
    if (stringLength == null) {
      throw new IllegalArgumentException("null value for 'stringLength' argument");
    }
    if (integer == null) {
      throw new IllegalArgumentException("null value for 'integer' argument");
    }
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
    if (stringLength == null) {
      throw new IllegalArgumentException("null value for 'stringLength' argument");
    }
    return new StringFacet_Sequence(stringLength, integer);
  }
  
  public StringFacet_Sequence withInteger(hydra.langs.shex.syntax.Integer_ integer) {
    if (integer == null) {
      throw new IllegalArgumentException("null value for 'integer' argument");
    }
    return new StringFacet_Sequence(stringLength, integer);
  }
}