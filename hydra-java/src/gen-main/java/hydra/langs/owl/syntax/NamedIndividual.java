package hydra.langs.owl.syntax;

import java.io.Serializable;

public class NamedIndividual implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.NamedIndividual");
  
  public NamedIndividual () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof NamedIndividual)) {
      return false;
    }
    NamedIndividual o = (NamedIndividual) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}