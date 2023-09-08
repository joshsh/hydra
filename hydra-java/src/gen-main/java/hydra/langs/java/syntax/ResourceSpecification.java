package hydra.langs.java.syntax;

import java.io.Serializable;

public class ResourceSpecification implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ResourceSpecification");
  
  public final java.util.List<hydra.langs.java.syntax.Resource> value;
  
  public ResourceSpecification (java.util.List<hydra.langs.java.syntax.Resource> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ResourceSpecification)) {
      return false;
    }
    ResourceSpecification o = (ResourceSpecification) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}