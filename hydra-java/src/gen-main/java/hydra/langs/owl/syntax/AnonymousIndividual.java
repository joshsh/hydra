package hydra.langs.owl.syntax;

import java.io.Serializable;

public class AnonymousIndividual implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.AnonymousIndividual");
  
  public AnonymousIndividual () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnonymousIndividual)) {
      return false;
    }
    AnonymousIndividual o = (AnonymousIndividual) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}