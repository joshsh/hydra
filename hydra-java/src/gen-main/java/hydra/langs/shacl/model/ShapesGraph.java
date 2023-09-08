package hydra.langs.shacl.model;

import java.io.Serializable;

/**
 * An RDF graph containing zero or more shapes that is passed into a SHACL validation process so that a data graph can be validated against the shapes
 */
public class ShapesGraph implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shacl/model.ShapesGraph");
  
  /**
   * An RDF graph containing zero or more shapes that is passed into a SHACL validation process so that a data graph can be validated against the shapes
   */
  public final java.util.Set<hydra.langs.shacl.model.Definition<hydra.langs.shacl.model.Shape>> value;
  
  public ShapesGraph (java.util.Set<hydra.langs.shacl.model.Definition<hydra.langs.shacl.model.Shape>> value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ShapesGraph)) {
      return false;
    }
    ShapesGraph o = (ShapesGraph) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}