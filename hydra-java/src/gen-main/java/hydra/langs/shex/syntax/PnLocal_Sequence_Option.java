package hydra.langs.shex.syntax;

import java.io.Serializable;

public class PnLocal_Sequence_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.PnLocal.Sequence.Option");
  
  public final java.util.List<hydra.langs.shex.syntax.PnLocal_Sequence_Option_ListOfAlts_Elmt> listOfAlts;
  
  public final hydra.langs.shex.syntax.PnLocal_Sequence_Option_Alts alts;
  
  public PnLocal_Sequence_Option (java.util.List<hydra.langs.shex.syntax.PnLocal_Sequence_Option_ListOfAlts_Elmt> listOfAlts, hydra.langs.shex.syntax.PnLocal_Sequence_Option_Alts alts) {
    this.listOfAlts = listOfAlts;
    this.alts = alts;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PnLocal_Sequence_Option)) {
      return false;
    }
    PnLocal_Sequence_Option o = (PnLocal_Sequence_Option) (other);
    return listOfAlts.equals(o.listOfAlts) && alts.equals(o.alts);
  }
  
  @Override
  public int hashCode() {
    return 2 * listOfAlts.hashCode() + 3 * alts.hashCode();
  }
  
  public PnLocal_Sequence_Option withListOfAlts(java.util.List<hydra.langs.shex.syntax.PnLocal_Sequence_Option_ListOfAlts_Elmt> listOfAlts) {
    return new PnLocal_Sequence_Option(listOfAlts, alts);
  }
  
  public PnLocal_Sequence_Option withAlts(hydra.langs.shex.syntax.PnLocal_Sequence_Option_Alts alts) {
    return new PnLocal_Sequence_Option(listOfAlts, alts);
  }
}