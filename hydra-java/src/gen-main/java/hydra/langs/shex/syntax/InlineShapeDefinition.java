// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class InlineShapeDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.InlineShapeDefinition");
  
  public final java.util.List<hydra.langs.shex.syntax.InlineShapeDefinition_ListOfAlts_Elmt> listOfAlts;
  
  public final java.util.Optional<hydra.langs.shex.syntax.TripleExpression> tripleExpression;
  
  public InlineShapeDefinition (java.util.List<hydra.langs.shex.syntax.InlineShapeDefinition_ListOfAlts_Elmt> listOfAlts, java.util.Optional<hydra.langs.shex.syntax.TripleExpression> tripleExpression) {
    if (listOfAlts == null) {
      throw new IllegalArgumentException("null value for 'listOfAlts' argument");
    }
    if (tripleExpression == null) {
      throw new IllegalArgumentException("null value for 'tripleExpression' argument");
    }
    this.listOfAlts = listOfAlts;
    this.tripleExpression = tripleExpression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof InlineShapeDefinition)) {
      return false;
    }
    InlineShapeDefinition o = (InlineShapeDefinition) (other);
    return listOfAlts.equals(o.listOfAlts) && tripleExpression.equals(o.tripleExpression);
  }
  
  @Override
  public int hashCode() {
    return 2 * listOfAlts.hashCode() + 3 * tripleExpression.hashCode();
  }
  
  public InlineShapeDefinition withListOfAlts(java.util.List<hydra.langs.shex.syntax.InlineShapeDefinition_ListOfAlts_Elmt> listOfAlts) {
    if (listOfAlts == null) {
      throw new IllegalArgumentException("null value for 'listOfAlts' argument");
    }
    return new InlineShapeDefinition(listOfAlts, tripleExpression);
  }
  
  public InlineShapeDefinition withTripleExpression(java.util.Optional<hydra.langs.shex.syntax.TripleExpression> tripleExpression) {
    if (tripleExpression == null) {
      throw new IllegalArgumentException("null value for 'tripleExpression' argument");
    }
    return new InlineShapeDefinition(listOfAlts, tripleExpression);
  }
}