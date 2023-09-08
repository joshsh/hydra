package hydra.langs.java.syntax;

import java.io.Serializable;

public class Wildcard implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.Wildcard");
  
  public final java.util.List<hydra.langs.java.syntax.Annotation> annotations;
  
  public final java.util.Optional<hydra.langs.java.syntax.WildcardBounds> wildcard;
  
  public Wildcard (java.util.List<hydra.langs.java.syntax.Annotation> annotations, java.util.Optional<hydra.langs.java.syntax.WildcardBounds> wildcard) {
    this.annotations = annotations;
    this.wildcard = wildcard;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Wildcard)) {
      return false;
    }
    Wildcard o = (Wildcard) (other);
    return annotations.equals(o.annotations) && wildcard.equals(o.wildcard);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * wildcard.hashCode();
  }
  
  public Wildcard withAnnotations(java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    return new Wildcard(annotations, wildcard);
  }
  
  public Wildcard withWildcard(java.util.Optional<hydra.langs.java.syntax.WildcardBounds> wildcard) {
    return new Wildcard(annotations, wildcard);
  }
}