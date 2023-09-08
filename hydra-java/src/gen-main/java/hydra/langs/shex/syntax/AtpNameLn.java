package hydra.langs.shex.syntax;

import java.io.Serializable;

public class AtpNameLn implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.AtpNameLn");
  
  public final hydra.langs.shex.syntax.PnameNs pnameNs;
  
  public final hydra.langs.shex.syntax.PnLocal pnLocal;
  
  public AtpNameLn (hydra.langs.shex.syntax.PnameNs pnameNs, hydra.langs.shex.syntax.PnLocal pnLocal) {
    this.pnameNs = pnameNs;
    this.pnLocal = pnLocal;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AtpNameLn)) {
      return false;
    }
    AtpNameLn o = (AtpNameLn) (other);
    return pnameNs.equals(o.pnameNs) && pnLocal.equals(o.pnLocal);
  }
  
  @Override
  public int hashCode() {
    return 2 * pnameNs.hashCode() + 3 * pnLocal.hashCode();
  }
  
  public AtpNameLn withPnameNs(hydra.langs.shex.syntax.PnameNs pnameNs) {
    return new AtpNameLn(pnameNs, pnLocal);
  }
  
  public AtpNameLn withPnLocal(hydra.langs.shex.syntax.PnLocal pnLocal) {
    return new AtpNameLn(pnameNs, pnLocal);
  }
}