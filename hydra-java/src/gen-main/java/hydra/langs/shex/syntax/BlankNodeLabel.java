// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class BlankNodeLabel implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/shex/syntax.BlankNodeLabel");
  
  public static final hydra.core.Name FIELD_NAME_ALTS = new hydra.core.Name("alts");
  
  public static final hydra.core.Name FIELD_NAME_LIST_OF_ALTS = new hydra.core.Name("listOfAlts");
  
  public static final hydra.core.Name FIELD_NAME_PN_CHARS = new hydra.core.Name("pnChars");
  
  public final hydra.langs.shex.syntax.BlankNodeLabel_Alts alts;
  
  public final hydra.util.Opt<java.util.List<hydra.langs.shex.syntax.BlankNodeLabel_ListOfAlts_Option_Elmt>> listOfAlts;
  
  public final hydra.langs.shex.syntax.PnChars pnChars;
  
  public BlankNodeLabel (hydra.langs.shex.syntax.BlankNodeLabel_Alts alts, hydra.util.Opt<java.util.List<hydra.langs.shex.syntax.BlankNodeLabel_ListOfAlts_Option_Elmt>> listOfAlts, hydra.langs.shex.syntax.PnChars pnChars) {
    java.util.Objects.requireNonNull((alts));
    java.util.Objects.requireNonNull((listOfAlts));
    java.util.Objects.requireNonNull((pnChars));
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
    java.util.Objects.requireNonNull((alts));
    return new BlankNodeLabel(alts, listOfAlts, pnChars);
  }
  
  public BlankNodeLabel withListOfAlts(hydra.util.Opt<java.util.List<hydra.langs.shex.syntax.BlankNodeLabel_ListOfAlts_Option_Elmt>> listOfAlts) {
    java.util.Objects.requireNonNull((listOfAlts));
    return new BlankNodeLabel(alts, listOfAlts, pnChars);
  }
  
  public BlankNodeLabel withPnChars(hydra.langs.shex.syntax.PnChars pnChars) {
    java.util.Objects.requireNonNull((pnChars));
    return new BlankNodeLabel(alts, listOfAlts, pnChars);
  }
}