package hydra.ext.shex.syntax;

public class StringLiteralLong1_ListOfAlts_Elmt_Sequence {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/shex/syntax.StringLiteralLong1.ListOfAlts.Elmt.Sequence");
  
  public final java.util.Optional<hydra.ext.shex.syntax.StringLiteralLong1_ListOfAlts_Elmt_Sequence_Alts_Option> alts;
  
  public final String regex;
  
  public StringLiteralLong1_ListOfAlts_Elmt_Sequence (java.util.Optional<hydra.ext.shex.syntax.StringLiteralLong1_ListOfAlts_Elmt_Sequence_Alts_Option> alts, String regex) {
    this.alts = alts;
    this.regex = regex;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StringLiteralLong1_ListOfAlts_Elmt_Sequence)) {
      return false;
    }
    StringLiteralLong1_ListOfAlts_Elmt_Sequence o = (StringLiteralLong1_ListOfAlts_Elmt_Sequence) (other);
    return alts.equals(o.alts) && regex.equals(o.regex);
  }
  
  @Override
  public int hashCode() {
    return 2 * alts.hashCode() + 3 * regex.hashCode();
  }
  
  public StringLiteralLong1_ListOfAlts_Elmt_Sequence withAlts(java.util.Optional<hydra.ext.shex.syntax.StringLiteralLong1_ListOfAlts_Elmt_Sequence_Alts_Option> alts) {
    return new StringLiteralLong1_ListOfAlts_Elmt_Sequence(alts, regex);
  }
  
  public StringLiteralLong1_ListOfAlts_Elmt_Sequence withRegex(String regex) {
    return new StringLiteralLong1_ListOfAlts_Elmt_Sequence(alts, regex);
  }
}