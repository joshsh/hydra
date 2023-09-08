package hydra.langs.shex.syntax;

import java.io.Serializable;

public class InlineShapeAnd implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.InlineShapeAnd");
  
  public final hydra.langs.shex.syntax.InlineShapeNot inlineShapeNot;
  
  public final java.util.List<hydra.langs.shex.syntax.InlineShapeNot> listOfSequence;
  
  public InlineShapeAnd (hydra.langs.shex.syntax.InlineShapeNot inlineShapeNot, java.util.List<hydra.langs.shex.syntax.InlineShapeNot> listOfSequence) {
    this.inlineShapeNot = inlineShapeNot;
    this.listOfSequence = listOfSequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InlineShapeAnd)) {
      return false;
    }
    InlineShapeAnd o = (InlineShapeAnd) (other);
    return inlineShapeNot.equals(o.inlineShapeNot) && listOfSequence.equals(o.listOfSequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * inlineShapeNot.hashCode() + 3 * listOfSequence.hashCode();
  }
  
  public InlineShapeAnd withInlineShapeNot(hydra.langs.shex.syntax.InlineShapeNot inlineShapeNot) {
    return new InlineShapeAnd(inlineShapeNot, listOfSequence);
  }
  
  public InlineShapeAnd withListOfSequence(java.util.List<hydra.langs.shex.syntax.InlineShapeNot> listOfSequence) {
    return new InlineShapeAnd(inlineShapeNot, listOfSequence);
  }
}