package hydra.langs.shex.syntax;

import java.io.Serializable;

public class NumericFacet_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.NumericFacet.Sequence2");
  
  public final hydra.langs.shex.syntax.NumericLength numericLength;
  
  public final hydra.langs.shex.syntax.Integer_ integer;
  
  public NumericFacet_Sequence2 (hydra.langs.shex.syntax.NumericLength numericLength, hydra.langs.shex.syntax.Integer_ integer) {
    this.numericLength = numericLength;
    this.integer = integer;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NumericFacet_Sequence2)) {
      return false;
    }
    NumericFacet_Sequence2 o = (NumericFacet_Sequence2) (other);
    return numericLength.equals(o.numericLength) && integer.equals(o.integer);
  }
  
  @Override
  public int hashCode() {
    return 2 * numericLength.hashCode() + 3 * integer.hashCode();
  }
  
  public NumericFacet_Sequence2 withNumericLength(hydra.langs.shex.syntax.NumericLength numericLength) {
    return new NumericFacet_Sequence2(numericLength, integer);
  }
  
  public NumericFacet_Sequence2 withInteger(hydra.langs.shex.syntax.Integer_ integer) {
    return new NumericFacet_Sequence2(numericLength, integer);
  }
}