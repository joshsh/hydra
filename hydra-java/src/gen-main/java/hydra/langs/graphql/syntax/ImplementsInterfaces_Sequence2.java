package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ImplementsInterfaces_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ImplementsInterfaces.Sequence2");
  
  public final java.util.Optional<java.lang.Void> amp;
  
  public final hydra.langs.graphql.syntax.NamedType namedType;
  
  public ImplementsInterfaces_Sequence2 (java.util.Optional<java.lang.Void> amp, hydra.langs.graphql.syntax.NamedType namedType) {
    this.amp = amp;
    this.namedType = namedType;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ImplementsInterfaces_Sequence2)) {
      return false;
    }
    ImplementsInterfaces_Sequence2 o = (ImplementsInterfaces_Sequence2) (other);
    return amp.equals(o.amp) && namedType.equals(o.namedType);
  }
  
  @Override
  public int hashCode() {
    return 2 * amp.hashCode() + 3 * namedType.hashCode();
  }
  
  public ImplementsInterfaces_Sequence2 withAmp(java.util.Optional<java.lang.Void> amp) {
    return new ImplementsInterfaces_Sequence2(amp, namedType);
  }
  
  public ImplementsInterfaces_Sequence2 withNamedType(hydra.langs.graphql.syntax.NamedType namedType) {
    return new ImplementsInterfaces_Sequence2(amp, namedType);
  }
}