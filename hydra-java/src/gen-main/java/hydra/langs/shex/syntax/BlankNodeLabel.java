package hydra.langs.shex.syntax;

import java.io.Serializable;

public class BlankNodeLabel implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.BlankNodeLabel");
  
  public final hydra.langs.shex.syntax.BlankNodeLabel_Alts alts;
  
  public final java.util.Optional<java.util.List<hydra.langs.shex.syntax.BlankNodeLabel_ListOfAlts_Option_Elmt>> listOfAlts;
  
  public final hydra.langs.shex.syntax.PnChars pnChars;
  
  public BlankNodeLabel (hydra.langs.shex.syntax.BlankNodeLabel_Alts alts, java.util.Optional<java.util.List<hydra.langs.shex.syntax.BlankNodeLabel_ListOfAlts_Option_Elmt>> listOfAlts, hydra.langs.shex.syntax.PnChars pnChars) {
    this.alts = alts;
    this.listOfAlts = listOfAlts;
    this.pnChars = pnChars;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BlankNodeLabel)) {
      return false;
    }
    BlankNodeLabel o = (BlankNodeLabel) (other);
    return alts.equals(o.alts) && listOfAlts.equals(o.listOfAlts) && pnChars.equals(o.pnChars);
  }
  
  @Override
  public int hashCode() {
    return 2 * alts.hashCode() + 3 * listOfAlts.hashCode() + 5 * pnChars.hashCode();
  }
  
  public BlankNodeLabel withAlts(hydra.langs.shex.syntax.BlankNodeLabel_Alts alts) {
    return new BlankNodeLabel(alts, listOfAlts, pnChars);
  }
  
  public BlankNodeLabel withListOfAlts(java.util.Optional<java.util.List<hydra.langs.shex.syntax.BlankNodeLabel_ListOfAlts_Option_Elmt>> listOfAlts) {
    return new BlankNodeLabel(alts, listOfAlts, pnChars);
  }
  
  public BlankNodeLabel withPnChars(hydra.langs.shex.syntax.PnChars pnChars) {
    return new BlankNodeLabel(alts, listOfAlts, pnChars);
  }
}