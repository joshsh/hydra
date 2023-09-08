package hydra.langs.shex.syntax;

import java.io.Serializable;

public class PnPrefix implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.PnPrefix");
  
  public final hydra.langs.shex.syntax.PnCharsBase pnCharsBase;
  
  public final java.util.Optional<hydra.langs.shex.syntax.PnPrefix_Sequence_Option> sequence;
  
  public PnPrefix (hydra.langs.shex.syntax.PnCharsBase pnCharsBase, java.util.Optional<hydra.langs.shex.syntax.PnPrefix_Sequence_Option> sequence) {
    this.pnCharsBase = pnCharsBase;
    this.sequence = sequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PnPrefix)) {
      return false;
    }
    PnPrefix o = (PnPrefix) (other);
    return pnCharsBase.equals(o.pnCharsBase) && sequence.equals(o.sequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * pnCharsBase.hashCode() + 3 * sequence.hashCode();
  }
  
  public PnPrefix withPnCharsBase(hydra.langs.shex.syntax.PnCharsBase pnCharsBase) {
    return new PnPrefix(pnCharsBase, sequence);
  }
  
  public PnPrefix withSequence(java.util.Optional<hydra.langs.shex.syntax.PnPrefix_Sequence_Option> sequence) {
    return new PnPrefix(pnCharsBase, sequence);
  }
}