package hydra.langs.shex.syntax;

import java.io.Serializable;

public class PrefixDecl implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.PrefixDecl");
  
  public final hydra.langs.shex.syntax.PnameNs pnameNs;
  
  public final hydra.langs.shex.syntax.IriRef iriRef;
  
  public PrefixDecl (hydra.langs.shex.syntax.PnameNs pnameNs, hydra.langs.shex.syntax.IriRef iriRef) {
    this.pnameNs = pnameNs;
    this.iriRef = iriRef;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PrefixDecl)) {
      return false;
    }
    PrefixDecl o = (PrefixDecl) (other);
    return pnameNs.equals(o.pnameNs) && iriRef.equals(o.iriRef);
  }
  
  @Override
  public int hashCode() {
    return 2 * pnameNs.hashCode() + 3 * iriRef.hashCode();
  }
  
  public PrefixDecl withPnameNs(hydra.langs.shex.syntax.PnameNs pnameNs) {
    return new PrefixDecl(pnameNs, iriRef);
  }
  
  public PrefixDecl withIriRef(hydra.langs.shex.syntax.IriRef iriRef) {
    return new PrefixDecl(pnameNs, iriRef);
  }
}