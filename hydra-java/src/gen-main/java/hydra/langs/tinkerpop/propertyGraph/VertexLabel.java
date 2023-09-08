package hydra.langs.tinkerpop.propertyGraph;

import java.io.Serializable;

/**
 * The label of a vertex. The default (null) vertex is represented by the empty string
 */
public class VertexLabel implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/propertyGraph.VertexLabel");
  
  /**
   * The label of a vertex. The default (null) vertex is represented by the empty string
   */
  public final String value;
  
  public VertexLabel (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof VertexLabel)) {
      return false;
    }
    VertexLabel o = (VertexLabel) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}