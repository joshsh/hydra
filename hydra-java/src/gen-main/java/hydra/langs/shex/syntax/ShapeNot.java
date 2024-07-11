// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class ShapeNot implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ShapeNot");
  
  public final hydra.util.Opt<java.lang.Void> nOT;
  
  public final hydra.langs.shex.syntax.ShapeAtom shapeAtom;
  
  public ShapeNot (hydra.util.Opt<java.lang.Void> nOT, hydra.langs.shex.syntax.ShapeAtom shapeAtom) {
    if (nOT == null) {
      throw new IllegalArgumentException("null value for 'nOT' argument");
    }
    if (shapeAtom == null) {
      throw new IllegalArgumentException("null value for 'shapeAtom' argument");
    }
    this.nOT = nOT;
    this.shapeAtom = shapeAtom;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ShapeNot)) {
      return false;
    }
    ShapeNot o = (ShapeNot) (other);
    return nOT.equals(o.nOT) && shapeAtom.equals(o.shapeAtom);
  }
  
  @Override
  public int hashCode() {
    return 2 * nOT.hashCode() + 3 * shapeAtom.hashCode();
  }
  
  public ShapeNot withNOT(hydra.util.Opt<java.lang.Void> nOT) {
    if (nOT == null) {
      throw new IllegalArgumentException("null value for 'nOT' argument");
    }
    return new ShapeNot(nOT, shapeAtom);
  }
  
  public ShapeNot withShapeAtom(hydra.langs.shex.syntax.ShapeAtom shapeAtom) {
    if (shapeAtom == null) {
      throw new IllegalArgumentException("null value for 'shapeAtom' argument");
    }
    return new ShapeNot(nOT, shapeAtom);
  }
}