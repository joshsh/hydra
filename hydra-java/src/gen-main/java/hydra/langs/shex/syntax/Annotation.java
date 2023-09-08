package hydra.langs.shex.syntax;

import java.io.Serializable;

public class Annotation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Annotation");
  
  public final hydra.langs.shex.syntax.Predicate predicate;
  
  public final hydra.langs.shex.syntax.Annotation_Alts alts;
  
  public Annotation (hydra.langs.shex.syntax.Predicate predicate, hydra.langs.shex.syntax.Annotation_Alts alts) {
    this.predicate = predicate;
    this.alts = alts;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Annotation)) {
      return false;
    }
    Annotation o = (Annotation) (other);
    return predicate.equals(o.predicate) && alts.equals(o.alts);
  }
  
  @Override
  public int hashCode() {
    return 2 * predicate.hashCode() + 3 * alts.hashCode();
  }
  
  public Annotation withPredicate(hydra.langs.shex.syntax.Predicate predicate) {
    return new Annotation(predicate, alts);
  }
  
  public Annotation withAlts(hydra.langs.shex.syntax.Annotation_Alts alts) {
    return new Annotation(predicate, alts);
  }
}