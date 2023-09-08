package hydra.langs.shex.syntax;

import java.io.Serializable;

public class BracketedTripleExpr implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.BracketedTripleExpr");
  
  public final hydra.langs.shex.syntax.InnerTripleExpr innerTripleExpr;
  
  public final java.util.Optional<hydra.langs.shex.syntax.Cardinality> cardinality;
  
  public final java.util.List<hydra.langs.shex.syntax.Annotation> listOfAnnotation;
  
  public final hydra.langs.shex.syntax.SemanticActions semanticActions;
  
  public BracketedTripleExpr (hydra.langs.shex.syntax.InnerTripleExpr innerTripleExpr, java.util.Optional<hydra.langs.shex.syntax.Cardinality> cardinality, java.util.List<hydra.langs.shex.syntax.Annotation> listOfAnnotation, hydra.langs.shex.syntax.SemanticActions semanticActions) {
    this.innerTripleExpr = innerTripleExpr;
    this.cardinality = cardinality;
    this.listOfAnnotation = listOfAnnotation;
    this.semanticActions = semanticActions;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BracketedTripleExpr)) {
      return false;
    }
    BracketedTripleExpr o = (BracketedTripleExpr) (other);
    return innerTripleExpr.equals(o.innerTripleExpr) && cardinality.equals(o.cardinality) && listOfAnnotation.equals(o.listOfAnnotation) && semanticActions.equals(o.semanticActions);
  }
  
  @Override
  public int hashCode() {
    return 2 * innerTripleExpr.hashCode() + 3 * cardinality.hashCode() + 5 * listOfAnnotation.hashCode() + 7 * semanticActions.hashCode();
  }
  
  public BracketedTripleExpr withInnerTripleExpr(hydra.langs.shex.syntax.InnerTripleExpr innerTripleExpr) {
    return new BracketedTripleExpr(innerTripleExpr, cardinality, listOfAnnotation, semanticActions);
  }
  
  public BracketedTripleExpr withCardinality(java.util.Optional<hydra.langs.shex.syntax.Cardinality> cardinality) {
    return new BracketedTripleExpr(innerTripleExpr, cardinality, listOfAnnotation, semanticActions);
  }
  
  public BracketedTripleExpr withListOfAnnotation(java.util.List<hydra.langs.shex.syntax.Annotation> listOfAnnotation) {
    return new BracketedTripleExpr(innerTripleExpr, cardinality, listOfAnnotation, semanticActions);
  }
  
  public BracketedTripleExpr withSemanticActions(hydra.langs.shex.syntax.SemanticActions semanticActions) {
    return new BracketedTripleExpr(innerTripleExpr, cardinality, listOfAnnotation, semanticActions);
  }
}