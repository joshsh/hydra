package hydra.langs.shex.syntax;

import java.io.Serializable;

public class RdfLiteral implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.RdfLiteral");
  
  public final hydra.langs.shex.syntax.String_ string;
  
  public final java.util.Optional<hydra.langs.shex.syntax.RdfLiteral_Alts_Option> alts;
  
  public RdfLiteral (hydra.langs.shex.syntax.String_ string, java.util.Optional<hydra.langs.shex.syntax.RdfLiteral_Alts_Option> alts) {
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
  
  public RdfLiteral withString(hydra.langs.shex.syntax.String_ string) {
    return new RdfLiteral(string, alts);
  }
  
  public RdfLiteral withAlts(java.util.Optional<hydra.langs.shex.syntax.RdfLiteral_Alts_Option> alts) {
    return new RdfLiteral(string, alts);
  }
}