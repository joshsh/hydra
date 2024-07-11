// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class MultiElementOneOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.MultiElementOneOf");
  
  public final hydra.langs.shex.syntax.GroupTripleExpr groupTripleExpr;
  
  public final java.util.List<hydra.langs.shex.syntax.GroupTripleExpr> listOfSequence;
  
  public MultiElementOneOf (hydra.langs.shex.syntax.GroupTripleExpr groupTripleExpr, java.util.List<hydra.langs.shex.syntax.GroupTripleExpr> listOfSequence) {
    java.util.Objects.requireNonNull((groupTripleExpr));
    java.util.Objects.requireNonNull((listOfSequence));
    this.groupTripleExpr = groupTripleExpr;
    this.listOfSequence = listOfSequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MultiElementOneOf)) {
      return false;
    }
    MultiElementOneOf o = (MultiElementOneOf) (other);
    return groupTripleExpr.equals(o.groupTripleExpr) && listOfSequence.equals(o.listOfSequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * groupTripleExpr.hashCode() + 3 * listOfSequence.hashCode();
  }
  
  public MultiElementOneOf withGroupTripleExpr(hydra.langs.shex.syntax.GroupTripleExpr groupTripleExpr) {
    java.util.Objects.requireNonNull((groupTripleExpr));
    return new MultiElementOneOf(groupTripleExpr, listOfSequence);
  }
  
  public MultiElementOneOf withListOfSequence(java.util.List<hydra.langs.shex.syntax.GroupTripleExpr> listOfSequence) {
    java.util.Objects.requireNonNull((listOfSequence));
    return new MultiElementOneOf(groupTripleExpr, listOfSequence);
  }
}