// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class InlineShapeAtom_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.InlineShapeAtom.Sequence2");
  
  public final hydra.langs.shex.syntax.InlineShapeOrRef inlineShapeOrRef;
  
  public final hydra.util.Opt<hydra.langs.shex.syntax.NodeConstraint> nodeConstraint;
  
  public InlineShapeAtom_Sequence2 (hydra.langs.shex.syntax.InlineShapeOrRef inlineShapeOrRef, hydra.util.Opt<hydra.langs.shex.syntax.NodeConstraint> nodeConstraint) {
    if (inlineShapeOrRef == null) {
      throw new IllegalArgumentException("null value for 'inlineShapeOrRef' argument");
    }
    if (nodeConstraint == null) {
      throw new IllegalArgumentException("null value for 'nodeConstraint' argument");
    }
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
    if (inlineShapeOrRef == null) {
      throw new IllegalArgumentException("null value for 'inlineShapeOrRef' argument");
    }
    return new InlineShapeAtom_Sequence2(inlineShapeOrRef, nodeConstraint);
  }
  
  public InlineShapeAtom_Sequence2 withNodeConstraint(hydra.util.Opt<hydra.langs.shex.syntax.NodeConstraint> nodeConstraint) {
    if (nodeConstraint == null) {
      throw new IllegalArgumentException("null value for 'nodeConstraint' argument");
    }
    return new InlineShapeAtom_Sequence2(inlineShapeOrRef, nodeConstraint);
  }
}