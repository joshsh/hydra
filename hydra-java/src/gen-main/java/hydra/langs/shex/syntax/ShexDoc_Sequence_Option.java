package hydra.langs.shex.syntax;

import java.io.Serializable;

public class ShexDoc_Sequence_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ShexDoc.Sequence.Option");
  
  public final hydra.langs.shex.syntax.ShexDoc_Sequence_Option_Alts alts;
  
  public final java.util.List<hydra.langs.shex.syntax.Statement> listOfStatement;
  
  public ShexDoc_Sequence_Option (hydra.langs.shex.syntax.ShexDoc_Sequence_Option_Alts alts, java.util.List<hydra.langs.shex.syntax.Statement> listOfStatement) {
    this.alts = alts;
    this.listOfStatement = listOfStatement;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ShexDoc_Sequence_Option)) {
      return false;
    }
    ShexDoc_Sequence_Option o = (ShexDoc_Sequence_Option) (other);
    return alts.equals(o.alts) && listOfStatement.equals(o.listOfStatement);
  }
  
  @Override
  public int hashCode() {
    return 2 * alts.hashCode() + 3 * listOfStatement.hashCode();
  }
  
  public ShexDoc_Sequence_Option withAlts(hydra.langs.shex.syntax.ShexDoc_Sequence_Option_Alts alts) {
    return new ShexDoc_Sequence_Option(alts, listOfStatement);
  }
  
  public ShexDoc_Sequence_Option withListOfStatement(java.util.List<hydra.langs.shex.syntax.Statement> listOfStatement) {
    return new ShexDoc_Sequence_Option(alts, listOfStatement);
  }
}