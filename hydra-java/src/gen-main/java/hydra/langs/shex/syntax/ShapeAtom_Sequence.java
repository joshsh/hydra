package hydra.langs.shex.syntax;

import java.io.Serializable;

public class ShapeAtom_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ShapeAtom.Sequence");
  
  public final hydra.langs.shex.syntax.NodeConstraint nodeConstraint;
  
  public final java.util.Optional<hydra.langs.shex.syntax.ShapeOrRef> shapeOrRef;
  
  public ShapeAtom_Sequence (hydra.langs.shex.syntax.NodeConstraint nodeConstraint, java.util.Optional<hydra.langs.shex.syntax.ShapeOrRef> shapeOrRef) {
    this.nodeConstraint = nodeConstraint;
    this.shapeOrRef = shapeOrRef;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ShapeAtom_Sequence)) {
      return false;
    }
    ShapeAtom_Sequence o = (ShapeAtom_Sequence) (other);
    return nodeConstraint.equals(o.nodeConstraint) && shapeOrRef.equals(o.shapeOrRef);
  }
  
  @Override
  public int hashCode() {
    return 2 * nodeConstraint.hashCode() + 3 * shapeOrRef.hashCode();
  }
  
  public ShapeAtom_Sequence withNodeConstraint(hydra.langs.shex.syntax.NodeConstraint nodeConstraint) {
    return new ShapeAtom_Sequence(nodeConstraint, shapeOrRef);
  }
  
  public ShapeAtom_Sequence withShapeOrRef(java.util.Optional<hydra.langs.shex.syntax.ShapeOrRef> shapeOrRef) {
    return new ShapeAtom_Sequence(nodeConstraint, shapeOrRef);
  }
}