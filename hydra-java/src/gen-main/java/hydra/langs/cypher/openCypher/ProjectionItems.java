// Note: this is an automatically generated file. Do not edit.

package hydra.langs.cypher.openCypher;

import java.io.Serializable;

public class ProjectionItems implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/cypher/openCypher.ProjectionItems");
  
  public final Boolean star;
  
  public final java.util.List<hydra.langs.cypher.openCypher.ProjectionItem> explicit;
  
  public ProjectionItems (Boolean star, java.util.List<hydra.langs.cypher.openCypher.ProjectionItem> explicit) {
    if (star == null) {
      throw new IllegalArgumentException("null value for 'star' argument");
    }
    if (explicit == null) {
      throw new IllegalArgumentException("null value for 'explicit' argument");
    }
    this.star = star;
    this.explicit = explicit;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ProjectionItems)) {
      return false;
    }
    ProjectionItems o = (ProjectionItems) (other);
    return star.equals(o.star) && explicit.equals(o.explicit);
  }
  
  @Override
  public int hashCode() {
    return 2 * star.hashCode() + 3 * explicit.hashCode();
  }
  
  public ProjectionItems withStar(Boolean star) {
    if (star == null) {
      throw new IllegalArgumentException("null value for 'star' argument");
    }
    return new ProjectionItems(star, explicit);
  }
  
  public ProjectionItems withExplicit(java.util.List<hydra.langs.cypher.openCypher.ProjectionItem> explicit) {
    if (explicit == null) {
      throw new IllegalArgumentException("null value for 'explicit' argument");
    }
    return new ProjectionItems(star, explicit);
  }
}