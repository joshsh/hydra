package hydra.langs.java.syntax;

import java.io.Serializable;

public class ReceiverParameter implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ReceiverParameter");
  
  public final java.util.List<hydra.langs.java.syntax.Annotation> annotations;
  
  public final hydra.langs.java.syntax.UnannType unannType;
  
  public final java.util.Optional<hydra.langs.java.syntax.Identifier> identifier;
  
  public ReceiverParameter (java.util.List<hydra.langs.java.syntax.Annotation> annotations, hydra.langs.java.syntax.UnannType unannType, java.util.Optional<hydra.langs.java.syntax.Identifier> identifier) {
    this.annotations = annotations;
    this.unannType = unannType;
    this.identifier = identifier;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ReceiverParameter)) {
      return false;
    }
    ReceiverParameter o = (ReceiverParameter) (other);
    return annotations.equals(o.annotations) && unannType.equals(o.unannType) && identifier.equals(o.identifier);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * unannType.hashCode() + 5 * identifier.hashCode();
  }
  
  public ReceiverParameter withAnnotations(java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    return new ReceiverParameter(annotations, unannType, identifier);
  }
  
  public ReceiverParameter withUnannType(hydra.langs.java.syntax.UnannType unannType) {
    return new ReceiverParameter(annotations, unannType, identifier);
  }
  
  public ReceiverParameter withIdentifier(java.util.Optional<hydra.langs.java.syntax.Identifier> identifier) {
    return new ReceiverParameter(annotations, unannType, identifier);
  }
}