package hydra.langs.owl.syntax;

import java.io.Serializable;

/**
 * See https://www.w3.org/TR/owl2-syntax/#Disjoint_Union_of_Class_Expressions
 */
public class DisjointUnion implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DisjointUnion");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.Class_ class_;
  
  public final java.util.List<hydra.langs.owl.syntax.ClassExpression> classes;
  
  public DisjointUnion (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.Class_ class_, java.util.List<hydra.langs.owl.syntax.ClassExpression> classes) {
    this.annotations = annotations;
    this.class_ = class_;
    this.classes = classes;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DisjointUnion)) {
      return false;
    }
    DisjointUnion o = (DisjointUnion) (other);
    return annotations.equals(o.annotations) && class_.equals(o.class_) && classes.equals(o.classes);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * class_.hashCode() + 5 * classes.hashCode();
  }
  
  public DisjointUnion withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new DisjointUnion(annotations, class_, classes);
  }
  
  public DisjointUnion withClass(hydra.langs.owl.syntax.Class_ class_) {
    return new DisjointUnion(annotations, class_, classes);
  }
  
  public DisjointUnion withClasses(java.util.List<hydra.langs.owl.syntax.ClassExpression> classes) {
    return new DisjointUnion(annotations, class_, classes);
  }
}