// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class UnaryTripleExpr_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.UnaryTripleExpr.Sequence");
  
  public final java.util.Optional<hydra.langs.shex.syntax.TripleExprLabel> sequence;
  
  public final hydra.langs.shex.syntax.UnaryTripleExpr_Sequence_Alts alts;
  
  public UnaryTripleExpr_Sequence (java.util.Optional<hydra.langs.shex.syntax.TripleExprLabel> sequence, hydra.langs.shex.syntax.UnaryTripleExpr_Sequence_Alts alts) {
    if (sequence == null) {
      throw new IllegalArgumentException("null value for 'sequence' argument");
    }
    if (alts == null) {
      throw new IllegalArgumentException("null value for 'alts' argument");
    }
    this.sequence = sequence;
    this.alts = alts;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnaryTripleExpr_Sequence)) {
      return false;
    }
    UnaryTripleExpr_Sequence o = (UnaryTripleExpr_Sequence) (other);
    return sequence.equals(o.sequence) && alts.equals(o.alts);
  }
  
  @Override
  public int hashCode() {
    return 2 * sequence.hashCode() + 3 * alts.hashCode();
  }
  
  public UnaryTripleExpr_Sequence withSequence(java.util.Optional<hydra.langs.shex.syntax.TripleExprLabel> sequence) {
    if (sequence == null) {
      throw new IllegalArgumentException("null value for 'sequence' argument");
    }
    return new UnaryTripleExpr_Sequence(sequence, alts);
  }
  
  public UnaryTripleExpr_Sequence withAlts(hydra.langs.shex.syntax.UnaryTripleExpr_Sequence_Alts alts) {
    if (alts == null) {
      throw new IllegalArgumentException("null value for 'alts' argument");
    }
    return new UnaryTripleExpr_Sequence(sequence, alts);
  }
}