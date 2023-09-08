package hydra.langs.scala.meta;

import java.io.Serializable;

public class Case implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Case");
  
  public final hydra.langs.scala.meta.Pat pat;
  
  public final java.util.Optional<hydra.langs.scala.meta.Data> cond;
  
  public final hydra.langs.scala.meta.Data body;
  
  public Case (hydra.langs.scala.meta.Pat pat, java.util.Optional<hydra.langs.scala.meta.Data> cond, hydra.langs.scala.meta.Data body) {
    this.pat = pat;
    this.cond = cond;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Case)) {
      return false;
    }
    Case o = (Case) (other);
    return pat.equals(o.pat) && cond.equals(o.cond) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * pat.hashCode() + 3 * cond.hashCode() + 5 * body.hashCode();
  }
  
  public Case withPat(hydra.langs.scala.meta.Pat pat) {
    return new Case(pat, cond, body);
  }
  
  public Case withCond(java.util.Optional<hydra.langs.scala.meta.Data> cond) {
    return new Case(pat, cond, body);
  }
  
  public Case withBody(hydra.langs.scala.meta.Data body) {
    return new Case(pat, cond, body);
  }
}