package hydra.langs.shex.syntax;

import java.io.Serializable;

public class IriRange_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.IriRange.Sequence");
  
  public final hydra.langs.shex.syntax.Iri iri;
  
  public final java.util.Optional<java.util.List<hydra.langs.shex.syntax.Exclusion>> sequence;
  
  public IriRange_Sequence (hydra.langs.shex.syntax.Iri iri, java.util.Optional<java.util.List<hydra.langs.shex.syntax.Exclusion>> sequence) {
    this.iri = iri;
    this.sequence = sequence;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IriRange_Sequence)) {
      return false;
    }
    IriRange_Sequence o = (IriRange_Sequence) (other);
    return iri.equals(o.iri) && sequence.equals(o.sequence);
  }
  
  @Override
  public int hashCode() {
    return 2 * iri.hashCode() + 3 * sequence.hashCode();
  }
  
  public IriRange_Sequence withIri(hydra.langs.shex.syntax.Iri iri) {
    return new IriRange_Sequence(iri, sequence);
  }
  
  public IriRange_Sequence withSequence(java.util.Optional<java.util.List<hydra.langs.shex.syntax.Exclusion>> sequence) {
    return new IriRange_Sequence(iri, sequence);
  }
}