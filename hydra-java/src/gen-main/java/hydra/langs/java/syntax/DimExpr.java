package hydra.langs.java.syntax;

import java.io.Serializable;

public class DimExpr implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.DimExpr");
  
  public final java.util.List<hydra.langs.java.syntax.Annotation> annotations;
  
  public final java.util.Optional<hydra.langs.java.syntax.Expression> expression;
  
  public DimExpr (java.util.List<hydra.langs.java.syntax.Annotation> annotations, java.util.Optional<hydra.langs.java.syntax.Expression> expression) {
    this.annotations = annotations;
    this.expression = expression;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DimExpr)) {
      return false;
    }
    DimExpr o = (DimExpr) (other);
    return annotations.equals(o.annotations) && expression.equals(o.expression);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * expression.hashCode();
  }
  
  public DimExpr withAnnotations(java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    return new DimExpr(annotations, expression);
  }
  
  public DimExpr withExpression(java.util.Optional<hydra.langs.java.syntax.Expression> expression) {
    return new DimExpr(annotations, expression);
  }
}