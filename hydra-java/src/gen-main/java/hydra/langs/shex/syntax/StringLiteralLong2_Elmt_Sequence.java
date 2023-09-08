package hydra.langs.shex.syntax;

import java.io.Serializable;

public class StringLiteralLong2_Elmt_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.StringLiteralLong2.Elmt.Sequence");
  
  public final java.util.Optional<hydra.langs.shex.syntax.StringLiteralLong2_Elmt_Sequence_Alts_Option> alts;
  
  public final String regex;
  
  public StringLiteralLong2_Elmt_Sequence (java.util.Optional<hydra.langs.shex.syntax.StringLiteralLong2_Elmt_Sequence_Alts_Option> alts, String regex) {
    this.alts = alts;
    this.regex = regex;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringLiteralLong2_Elmt_Sequence)) {
      return false;
    }
    StringLiteralLong2_Elmt_Sequence o = (StringLiteralLong2_Elmt_Sequence) (other);
    return alts.equals(o.alts) && regex.equals(o.regex);
  }
  
  @Override
  public int hashCode() {
    return 2 * alts.hashCode() + 3 * regex.hashCode();
  }
  
  public StringLiteralLong2_Elmt_Sequence withAlts(java.util.Optional<hydra.langs.shex.syntax.StringLiteralLong2_Elmt_Sequence_Alts_Option> alts) {
    return new StringLiteralLong2_Elmt_Sequence(alts, regex);
  }
  
  public StringLiteralLong2_Elmt_Sequence withRegex(String regex) {
    return new StringLiteralLong2_Elmt_Sequence(alts, regex);
  }
}