package hydra.langs.shex.syntax;

import java.io.Serializable;

public class NumericFacet_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.NumericFacet.Sequence");
  
  public final hydra.langs.shex.syntax.NumericRange numericRange;
  
  public final hydra.langs.shex.syntax.NumericLiteral numericLiteral;
  
  public NumericFacet_Sequence (hydra.langs.shex.syntax.NumericRange numericRange, hydra.langs.shex.syntax.NumericLiteral numericLiteral) {
    this.numericRange = numericRange;
    this.numericLiteral = numericLiteral;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NumericFacet_Sequence)) {
      return false;
    }
    NumericFacet_Sequence o = (NumericFacet_Sequence) (other);
    return numericRange.equals(o.numericRange) && numericLiteral.equals(o.numericLiteral);
  }
  
  @Override
  public int hashCode() {
    return 2 * numericRange.hashCode() + 3 * numericLiteral.hashCode();
  }
  
  public NumericFacet_Sequence withNumericRange(hydra.langs.shex.syntax.NumericRange numericRange) {
    return new NumericFacet_Sequence(numericRange, numericLiteral);
  }
  
  public NumericFacet_Sequence withNumericLiteral(hydra.langs.shex.syntax.NumericLiteral numericLiteral) {
    return new NumericFacet_Sequence(numericRange, numericLiteral);
  }
}