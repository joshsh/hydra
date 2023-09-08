package hydra.langs.tinkerpop.mappings;

import java.io.Serializable;

/**
 * A mapping specification producing edges of a specified label.
 */
public class EdgeSpec implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/mappings.EdgeSpec");
  
  /**
   * The label of the target edges, which must conform to the edge type associated with that label.
   */
  public final hydra.langs.tinkerpop.propertyGraph.EdgeLabel label;
  
  /**
   * A specification of the id of each target edge
   */
  public final hydra.langs.tinkerpop.mappings.ValueSpec id;
  
  /**
   * A specification of the out-vertex reference of each target edge
   */
  public final hydra.langs.tinkerpop.mappings.ValueSpec out;
  
  /**
   * A specification of the in-vertex reference of each target edge
   */
  public final hydra.langs.tinkerpop.mappings.ValueSpec in;
  
  /**
   * Zero or more property specifications for each target edge
   */
  public final java.util.List<hydra.langs.tinkerpop.mappings.PropertySpec> properties;
  
  public EdgeSpec (hydra.langs.tinkerpop.propertyGraph.EdgeLabel label, hydra.langs.tinkerpop.mappings.ValueSpec id, hydra.langs.tinkerpop.mappings.ValueSpec out, hydra.langs.tinkerpop.mappings.ValueSpec in, java.util.List<hydra.langs.tinkerpop.mappings.PropertySpec> properties) {
    this.label = label;
    this.id = id;
    this.out = out;
    this.in = in;
    this.properties = properties;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EdgeSpec)) {
      return false;
    }
    EdgeSpec o = (EdgeSpec) (other);
    return label.equals(o.label) && id.equals(o.id) && out.equals(o.out) && in.equals(o.in) && properties.equals(o.properties);
  }
  
  @Override
  public int hashCode() {
    return 2 * label.hashCode() + 3 * id.hashCode() + 5 * out.hashCode() + 7 * in.hashCode() + 11 * properties.hashCode();
  }
  
  public EdgeSpec withLabel(hydra.langs.tinkerpop.propertyGraph.EdgeLabel label) {
    return new EdgeSpec(label, id, out, in, properties);
  }
  
  public EdgeSpec withId(hydra.langs.tinkerpop.mappings.ValueSpec id) {
    return new EdgeSpec(label, id, out, in, properties);
  }
  
  public EdgeSpec withOut(hydra.langs.tinkerpop.mappings.ValueSpec out) {
    return new EdgeSpec(label, id, out, in, properties);
  }
  
  public EdgeSpec withIn(hydra.langs.tinkerpop.mappings.ValueSpec in) {
    return new EdgeSpec(label, id, out, in, properties);
  }
  
  public EdgeSpec withProperties(java.util.List<hydra.langs.tinkerpop.mappings.PropertySpec> properties) {
    return new EdgeSpec(label, id, out, in, properties);
  }
}