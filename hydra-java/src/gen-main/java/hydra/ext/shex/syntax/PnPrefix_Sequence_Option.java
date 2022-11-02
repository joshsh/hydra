package hydra.ext.shex.syntax;

public class PnPrefix_Sequence_Option {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/shex/syntax.PnPrefix.Sequence.Option");
  
  public final hydra.ext.shex.syntax.PnPrefix_Sequence_Option_Alts alts;
  
  public final hydra.ext.shex.syntax.PnChars pnChars;
  
  public PnPrefix_Sequence_Option (hydra.ext.shex.syntax.PnPrefix_Sequence_Option_Alts alts, hydra.ext.shex.syntax.PnChars pnChars) {
    this.alts = alts;
    this.pnChars = pnChars;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PnPrefix_Sequence_Option)) {
      return false;
    }
    PnPrefix_Sequence_Option o = (PnPrefix_Sequence_Option) (other);
    return alts.equals(o.alts) && pnChars.equals(o.pnChars);
  }
  
  @Override
  public int hashCode() {
    return 2 * alts.hashCode() + 3 * pnChars.hashCode();
  }
  
  public PnPrefix_Sequence_Option withAlts(hydra.ext.shex.syntax.PnPrefix_Sequence_Option_Alts alts) {
    return new PnPrefix_Sequence_Option(alts, pnChars);
  }
  
  public PnPrefix_Sequence_Option withPnChars(hydra.ext.shex.syntax.PnChars pnChars) {
    return new PnPrefix_Sequence_Option(alts, pnChars);
  }
}