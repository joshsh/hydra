package hydra.ext.shex.syntax;

public class CodeDecl {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/shex/syntax.CodeDecl");
  
  public final hydra.ext.shex.syntax.Iri iri;
  
  public final hydra.ext.shex.syntax.CodeDecl_Alts alts;
  
  public CodeDecl (hydra.ext.shex.syntax.Iri iri, hydra.ext.shex.syntax.CodeDecl_Alts alts) {
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
  
  public CodeDecl withIri(hydra.ext.shex.syntax.Iri iri) {
    return new CodeDecl(iri, alts);
  }
  
  public CodeDecl withAlts(hydra.ext.shex.syntax.CodeDecl_Alts alts) {
    return new CodeDecl(iri, alts);
  }
}