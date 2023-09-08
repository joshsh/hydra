package hydra.langs.shex.syntax;

import java.io.Serializable;

public class CodeDecl implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.CodeDecl");
  
  public final hydra.langs.shex.syntax.Iri iri;
  
  public final hydra.langs.shex.syntax.CodeDecl_Alts alts;
  
  public CodeDecl (hydra.langs.shex.syntax.Iri iri, hydra.langs.shex.syntax.CodeDecl_Alts alts) {
    this.iri = iri;
    this.alts = alts;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CodeDecl)) {
      return false;
    }
    CodeDecl o = (CodeDecl) (other);
    return iri.equals(o.iri) && alts.equals(o.alts);
  }
  
  @Override
  public int hashCode() {
    return 2 * iri.hashCode() + 3 * alts.hashCode();
  }
  
  public CodeDecl withIri(hydra.langs.shex.syntax.Iri iri) {
    return new CodeDecl(iri, alts);
  }
  
  public CodeDecl withAlts(hydra.langs.shex.syntax.CodeDecl_Alts alts) {
    return new CodeDecl(iri, alts);
  }
}