package hydra.langs.shex.syntax;

import java.io.Serializable;

public class RepeatRange implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.RepeatRange");
  
  public final hydra.langs.shex.syntax.Integer_ integer;
  
  public final java.util.Optional<java.util.Optional<java.util.Optional<hydra.langs.shex.syntax.RepeatRange_Sequence_Option_Option_Option>>> sequence;
  
  public RepeatRange (hydra.langs.shex.syntax.Integer_ integer, java.util.Optional<java.util.Optional<java.util.Optional<hydra.langs.shex.syntax.RepeatRange_Sequence_Option_Option_Option>>> sequence) {
    this.integer = integer;
    this.sequence = sequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RepeatRange)) {
      return false;
    }
    RepeatRange o = (RepeatRange) (other);
    return integer.equals(o.integer) && sequence.equals(o.sequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * integer.hashCode() + 3 * sequence.hashCode();
  }
  
  public RepeatRange withInteger(hydra.langs.shex.syntax.Integer_ integer) {
    return new RepeatRange(integer, sequence);
  }
  
  public RepeatRange withSequence(java.util.Optional<java.util.Optional<java.util.Optional<hydra.langs.shex.syntax.RepeatRange_Sequence_Option_Option_Option>>> sequence) {
    return new RepeatRange(integer, sequence);
  }
}