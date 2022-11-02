package hydra.ext.shex.syntax;

public class RdfLiteral {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/shex/syntax.RdfLiteral");
  
  public final hydra.ext.shex.syntax.String_ string;
  
  public final java.util.Optional<hydra.ext.shex.syntax.RdfLiteral_Alts_Option> alts;
  
  public RdfLiteral (hydra.ext.shex.syntax.String_ string, java.util.Optional<hydra.ext.shex.syntax.RdfLiteral_Alts_Option> alts) {
    this.string = string;
    this.alts = alts;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RdfLiteral)) {
      return false;
    }
    RdfLiteral o = (RdfLiteral) (other);
    return string.equals(o.string) && alts.equals(o.alts);
  }
  
  @Override
  public int hashCode() {
    return 2 * string.hashCode() + 3 * alts.hashCode();
  }
  
  public RdfLiteral withString(hydra.ext.shex.syntax.String_ string) {
    return new RdfLiteral(string, alts);
  }
  
  public RdfLiteral withAlts(java.util.Optional<hydra.ext.shex.syntax.RdfLiteral_Alts_Option> alts) {
    return new RdfLiteral(string, alts);
  }
}