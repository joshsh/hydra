package hydra.langs.shex.syntax;

import java.io.Serializable;

public class ShexDoc implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ShexDoc");
  
  public final java.util.List<hydra.langs.shex.syntax.Directive> listOfDirective;
  
  public final java.util.Optional<hydra.langs.shex.syntax.ShexDoc_Sequence_Option> sequence;
  
  public final hydra.langs.shex.syntax.PrefixDecl prefixDecl;
  
  public ShexDoc (java.util.List<hydra.langs.shex.syntax.Directive> listOfDirective, java.util.Optional<hydra.langs.shex.syntax.ShexDoc_Sequence_Option> sequence, hydra.langs.shex.syntax.PrefixDecl prefixDecl) {
    this.listOfDirective = listOfDirective;
    this.sequence = sequence;
    this.prefixDecl = prefixDecl;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ShexDoc)) {
      return false;
    }
    ShexDoc o = (ShexDoc) (other);
    return listOfDirective.equals(o.listOfDirective) && sequence.equals(o.sequence) && prefixDecl.equals(o.prefixDecl);
  }
  
  @Override
  public int hashCode() {
    return 2 * listOfDirective.hashCode() + 3 * sequence.hashCode() + 5 * prefixDecl.hashCode();
  }
  
  public ShexDoc withListOfDirective(java.util.List<hydra.langs.shex.syntax.Directive> listOfDirective) {
    return new ShexDoc(listOfDirective, sequence, prefixDecl);
  }
  
  public ShexDoc withSequence(java.util.Optional<hydra.langs.shex.syntax.ShexDoc_Sequence_Option> sequence) {
    return new ShexDoc(listOfDirective, sequence, prefixDecl);
  }
  
  public ShexDoc withPrefixDecl(hydra.langs.shex.syntax.PrefixDecl prefixDecl) {
    return new ShexDoc(listOfDirective, sequence, prefixDecl);
  }
}