package hydra.langs.shex.syntax;

import java.io.Serializable;

public class InlineShapeAtom_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.InlineShapeAtom.Sequence2");
  
  public final hydra.langs.shex.syntax.InlineShapeOrRef inlineShapeOrRef;
  
  public final java.util.Optional<hydra.langs.shex.syntax.NodeConstraint> nodeConstraint;
  
  public InlineShapeAtom_Sequence2 (hydra.langs.shex.syntax.InlineShapeOrRef inlineShapeOrRef, java.util.Optional<hydra.langs.shex.syntax.NodeConstraint> nodeConstraint) {
    this.inlineShapeOrRef = inlineShapeOrRef;
    this.nodeConstraint = nodeConstraint;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InlineShapeAtom_Sequence2)) {
      return false;
    }
    InlineShapeAtom_Sequence2 o = (InlineShapeAtom_Sequence2) (other);
    return inlineShapeOrRef.equals(o.inlineShapeOrRef) && nodeConstraint.equals(o.nodeConstraint);
  }
  
  @Override
  public int hashCode() {
    return 2 * inlineShapeOrRef.hashCode() + 3 * nodeConstraint.hashCode();
  }
  
  public InlineShapeAtom_Sequence2 withInlineShapeOrRef(hydra.langs.shex.syntax.InlineShapeOrRef inlineShapeOrRef) {
    return new InlineShapeAtom_Sequence2(inlineShapeOrRef, nodeConstraint);
  }
  
  public InlineShapeAtom_Sequence2 withNodeConstraint(java.util.Optional<hydra.langs.shex.syntax.NodeConstraint> nodeConstraint) {
    return new InlineShapeAtom_Sequence2(inlineShapeOrRef, nodeConstraint);
  }
}