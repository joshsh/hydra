package hydra.langs.shex.syntax;

import java.io.Serializable;

public class NodeConstraint_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.NodeConstraint.Sequence2");
  
  public final hydra.langs.shex.syntax.NonLiteralKind nonLiteralKind;
  
  public final java.util.List<hydra.langs.shex.syntax.StringFacet> listOfStringFacet;
  
  public NodeConstraint_Sequence2 (hydra.langs.shex.syntax.NonLiteralKind nonLiteralKind, java.util.List<hydra.langs.shex.syntax.StringFacet> listOfStringFacet) {
    this.nonLiteralKind = nonLiteralKind;
    this.listOfStringFacet = listOfStringFacet;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NodeConstraint_Sequence2)) {
      return false;
    }
    NodeConstraint_Sequence2 o = (NodeConstraint_Sequence2) (other);
    return nonLiteralKind.equals(o.nonLiteralKind) && listOfStringFacet.equals(o.listOfStringFacet);
  }
  
  @Override
  public int hashCode() {
    return 2 * nonLiteralKind.hashCode() + 3 * listOfStringFacet.hashCode();
  }
  
  public NodeConstraint_Sequence2 withNonLiteralKind(hydra.langs.shex.syntax.NonLiteralKind nonLiteralKind) {
    return new NodeConstraint_Sequence2(nonLiteralKind, listOfStringFacet);
  }
  
  public NodeConstraint_Sequence2 withListOfStringFacet(java.util.List<hydra.langs.shex.syntax.StringFacet> listOfStringFacet) {
    return new NodeConstraint_Sequence2(nonLiteralKind, listOfStringFacet);
  }
}