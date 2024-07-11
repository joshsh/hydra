// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class PnPrefix implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.PnPrefix");
  
  public final hydra.langs.shex.syntax.PnCharsBase pnCharsBase;
  
  public final hydra.util.Opt<hydra.langs.shex.syntax.PnPrefix_Sequence_Option> sequence;
  
  public PnPrefix (hydra.langs.shex.syntax.PnCharsBase pnCharsBase, hydra.util.Opt<hydra.langs.shex.syntax.PnPrefix_Sequence_Option> sequence) {
    if (pnCharsBase == null) {
      throw new IllegalArgumentException("null value for 'pnCharsBase' argument");
    }
    if (sequence == null) {
      throw new IllegalArgumentException("null value for 'sequence' argument");
    }
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
    if (pnCharsBase == null) {
      throw new IllegalArgumentException("null value for 'pnCharsBase' argument");
    }
    return new PnPrefix(pnCharsBase, sequence);
  }
  
  public PnPrefix withSequence(hydra.util.Opt<hydra.langs.shex.syntax.PnPrefix_Sequence_Option> sequence) {
    if (sequence == null) {
      throw new IllegalArgumentException("null value for 'sequence' argument");
    }
    return new PnPrefix(pnCharsBase, sequence);
  }
}