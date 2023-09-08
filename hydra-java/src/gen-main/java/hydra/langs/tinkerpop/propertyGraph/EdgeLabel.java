package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * The label of an edge
 */
public class EdgeLabel implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.EdgeLabel");
  
  /**
   * The label of an edge
   */
  public final String value;
  
  public EdgeLabel (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EdgeLabel)) {
      return false;
    }
    EdgeLabel o = (EdgeLabel) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}