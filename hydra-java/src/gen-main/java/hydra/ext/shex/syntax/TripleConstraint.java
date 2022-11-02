package hydra.ext.shex.syntax;

public class TripleConstraint {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/shex/syntax.TripleConstraint");
  
  public final java.util.Optional<hydra.ext.shex.syntax.SenseFlags> senseFlags;
  
  public final hydra.ext.shex.syntax.Predicate predicate;
  
  public final hydra.ext.shex.syntax.InlineShapeExpression inlineShapeExpression;
  
  public final java.util.Optional<hydra.ext.shex.syntax.Cardinality> cardinality;
  
  public final java.util.List<hydra.ext.shex.syntax.Annotation> listOfAnnotation;
  
  public final hydra.ext.shex.syntax.SemanticActions semanticActions;
  
  public TripleConstraint (java.util.Optional<hydra.ext.shex.syntax.SenseFlags> senseFlags, hydra.ext.shex.syntax.Predicate predicate, hydra.ext.shex.syntax.InlineShapeExpression inlineShapeExpression, java.util.Optional<hydra.ext.shex.syntax.Cardinality> cardinality, java.util.List<hydra.ext.shex.syntax.Annotation> listOfAnnotation, hydra.ext.shex.syntax.SemanticActions semanticActions) {
    this.senseFlags = senseFlags;
    this.predicate = predicate;
    this.inlineShapeExpression = inlineShapeExpression;
    this.cardinality = cardinality;
    this.listOfAnnotation = listOfAnnotation;
    this.semanticActions = semanticActions;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TripleConstraint)) {
      return false;
    }
    TripleConstraint o = (TripleConstraint) (other);
    return senseFlags.equals(o.senseFlags) && predicate.equals(o.predicate) && inlineShapeExpression.equals(o.inlineShapeExpression) && cardinality.equals(o.cardinality) && listOfAnnotation.equals(o.listOfAnnotation) && semanticActions.equals(o.semanticActions);
  }
  
  @Override
  public int hashCode() {
    return 2 * senseFlags.hashCode() + 3 * predicate.hashCode() + 5 * inlineShapeExpression.hashCode() + 7 * cardinality.hashCode() + 11 * listOfAnnotation.hashCode() + 13 * semanticActions.hashCode();
  }
  
  public TripleConstraint withSenseFlags(java.util.Optional<hydra.ext.shex.syntax.SenseFlags> senseFlags) {
    return new TripleConstraint(senseFlags, predicate, inlineShapeExpression, cardinality, listOfAnnotation, semanticActions);
  }
  
  public TripleConstraint withPredicate(hydra.ext.shex.syntax.Predicate predicate) {
    return new TripleConstraint(senseFlags, predicate, inlineShapeExpression, cardinality, listOfAnnotation, semanticActions);
  }
  
  public TripleConstraint withInlineShapeExpression(hydra.ext.shex.syntax.InlineShapeExpression inlineShapeExpression) {
    return new TripleConstraint(senseFlags, predicate, inlineShapeExpression, cardinality, listOfAnnotation, semanticActions);
  }
  
  public TripleConstraint withCardinality(java.util.Optional<hydra.ext.shex.syntax.Cardinality> cardinality) {
    return new TripleConstraint(senseFlags, predicate, inlineShapeExpression, cardinality, listOfAnnotation, semanticActions);
  }
  
  public TripleConstraint withListOfAnnotation(java.util.List<hydra.ext.shex.syntax.Annotation> listOfAnnotation) {
    return new TripleConstraint(senseFlags, predicate, inlineShapeExpression, cardinality, listOfAnnotation, semanticActions);
  }
  
  public TripleConstraint withSemanticActions(hydra.ext.shex.syntax.SemanticActions semanticActions) {
    return new TripleConstraint(senseFlags, predicate, inlineShapeExpression, cardinality, listOfAnnotation, semanticActions);
  }
}