package hydra.langs.shex.syntax;

import java.io.Serializable;

public class NodeConstraint_Sequence4 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.NodeConstraint.Sequence4");
  
  public final hydra.langs.shex.syntax.ValueSet valueSet;
  
  public final java.util.List<hydra.langs.shex.syntax.XsFacet> listOfXsFacet;
  
  public NodeConstraint_Sequence4 (hydra.langs.shex.syntax.ValueSet valueSet, java.util.List<hydra.langs.shex.syntax.XsFacet> listOfXsFacet) {
    this.valueSet = valueSet;
    this.listOfXsFacet = listOfXsFacet;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NodeConstraint_Sequence4)) {
      return false;
    }
    NodeConstraint_Sequence4 o = (NodeConstraint_Sequence4) (other);
    return valueSet.equals(o.valueSet) && listOfXsFacet.equals(o.listOfXsFacet);
  }
  
  @Override
  public int hashCode() {
    return 2 * valueSet.hashCode() + 3 * listOfXsFacet.hashCode();
  }
  
  public NodeConstraint_Sequence4 withValueSet(hydra.langs.shex.syntax.ValueSet valueSet) {
    return new NodeConstraint_Sequence4(valueSet, listOfXsFacet);
  }
  
  public NodeConstraint_Sequence4 withListOfXsFacet(java.util.List<hydra.langs.shex.syntax.XsFacet> listOfXsFacet) {
    return new NodeConstraint_Sequence4(valueSet, listOfXsFacet);
  }
}