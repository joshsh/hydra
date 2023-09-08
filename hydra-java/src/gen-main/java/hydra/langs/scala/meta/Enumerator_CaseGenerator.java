package hydra.langs.scala.meta;

import java.io.Serializable;

public class Enumerator_CaseGenerator implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Enumerator.CaseGenerator");
  
  public final hydra.langs.scala.meta.Pat pat;
  
  public final hydra.langs.scala.meta.Data rhs;
  
  public Enumerator_CaseGenerator (hydra.langs.scala.meta.Pat pat, hydra.langs.scala.meta.Data rhs) {
    this.pat = pat;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Enumerator_CaseGenerator)) {
      return false;
    }
    Enumerator_CaseGenerator o = (Enumerator_CaseGenerator) (other);
    return pat.equals(o.pat) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * pat.hashCode() + 3 * rhs.hashCode();
  }
  
  public Enumerator_CaseGenerator withPat(hydra.langs.scala.meta.Pat pat) {
    return new Enumerator_CaseGenerator(pat, rhs);
  }
  
  public Enumerator_CaseGenerator withRhs(hydra.langs.scala.meta.Data rhs) {
    return new Enumerator_CaseGenerator(pat, rhs);
  }
}