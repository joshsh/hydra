package hydra.langs.owl.syntax;

import java.io.Serializable;

public class SubClassOf implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.SubClassOf");
  
  public final java.util.List<hydra.langs.owl.syntax.Annotation> annotations;
  
  public final hydra.langs.owl.syntax.ClassExpression subClass;
  
  public final hydra.langs.owl.syntax.ClassExpression superClass;
  
  public SubClassOf (java.util.List<hydra.langs.owl.syntax.Annotation> annotations, hydra.langs.owl.syntax.ClassExpression subClass, hydra.langs.owl.syntax.ClassExpression superClass) {
    this.annotations = annotations;
    this.subClass = subClass;
    this.superClass = superClass;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SubClassOf)) {
      return false;
    }
    SubClassOf o = (SubClassOf) (other);
    return annotations.equals(o.annotations) && subClass.equals(o.subClass) && superClass.equals(o.superClass);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * subClass.hashCode() + 5 * superClass.hashCode();
  }
  
  public SubClassOf withAnnotations(java.util.List<hydra.langs.owl.syntax.Annotation> annotations) {
    return new SubClassOf(annotations, subClass, superClass);
  }
  
  public SubClassOf withSubClass(hydra.langs.owl.syntax.ClassExpression subClass) {
    return new SubClassOf(annotations, subClass, superClass);
  }
  
  public SubClassOf withSuperClass(hydra.langs.owl.syntax.ClassExpression superClass) {
    return new SubClassOf(annotations, subClass, superClass);
  }
}