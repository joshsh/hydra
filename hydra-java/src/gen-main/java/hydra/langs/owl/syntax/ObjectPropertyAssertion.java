package hydra.langs.owl.syntax;

import java.io.Serializable;

public class ObjectPropertyAssertion implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectPropertyAssertion");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public final hydra.langs.owl.syntax.Individual source;
  
  public final hydra.langs.owl.syntax.Individual target;
  
  public ObjectPropertyAssertion (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.ObjectPropertyExpression property, hydra.langs.owl.syntax.Individual source, hydra.langs.owl.syntax.Individual target) {
    this.annotations = annotations;
    this.property = property;
    this.source = source;
    this.target = target;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectPropertyAssertion)) {
      return false;
    }
    ObjectPropertyAssertion o = (ObjectPropertyAssertion) (other);
    return annotations.equals(o.annotations) && property.equals(o.property) && source.equals(o.source) && target.equals(o.target);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * property.hashCode() + 5 * source.hashCode() + 7 * target.hashCode();
  }
  
  public ObjectPropertyAssertion withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new ObjectPropertyAssertion(annotations, property, source, target);
  }
  
  public ObjectPropertyAssertion withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    return new ObjectPropertyAssertion(annotations, property, source, target);
  }
  
  public ObjectPropertyAssertion withSource(hydra.langs.owl.syntax.Individual source) {
    return new ObjectPropertyAssertion(annotations, property, source, target);
  }
  
  public ObjectPropertyAssertion withTarget(hydra.langs.owl.syntax.Individual target) {
    return new ObjectPropertyAssertion(annotations, property, source, target);
  }
}