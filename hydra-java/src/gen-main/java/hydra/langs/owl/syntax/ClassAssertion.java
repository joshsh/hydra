package hydra.langs.owl.syntax;

import java.io.Serializable;

public class ClassAssertion implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ClassAssertion");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.ClassExpression class_;
  
  public final hydra.langs.owl.syntax.Individual individual;
  
  public ClassAssertion (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.ClassExpression class_, hydra.langs.owl.syntax.Individual individual) {
    this.annotations = annotations;
    this.class_ = class_;
    this.individual = individual;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ClassAssertion)) {
      return false;
    }
    ClassAssertion o = (ClassAssertion) (other);
    return annotations.equals(o.annotations) && class_.equals(o.class_) && individual.equals(o.individual);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * class_.hashCode() + 5 * individual.hashCode();
  }
  
  public ClassAssertion withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new ClassAssertion(annotations, class_, individual);
  }
  
  public ClassAssertion withClass(hydra.langs.owl.syntax.ClassExpression class_) {
    return new ClassAssertion(annotations, class_, individual);
  }
  
  public ClassAssertion withIndividual(hydra.langs.owl.syntax.Individual individual) {
    return new ClassAssertion(annotations, class_, individual);
  }
}