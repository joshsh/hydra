package hydra.langs.tinkerpop.features;

import java.io.Serializable;

/**
 * Features that are related to Vertex operations.
 */
public class VertexFeatures implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/features.VertexFeatures");
  
  public final hydra.langs.tinkerpop.features.ElementFeatures elementFeatures;
  
  public final hydra.langs.tinkerpop.features.VertexPropertyFeatures properties;
  
  /**
   * Determines if a Vertex can be added to the Graph.
   */
  public final Boolean supportsAddVertices;
  
  /**
   * Determines if a Vertex can support non-unique values on the same key.
   */
  public final Boolean supportsDuplicateMultiProperties;
  
  /**
   * Determines if a Vertex can support properties on vertex properties.
   */
  public final Boolean supportsMetaProperties;
  
  /**
   * Determines if a Vertex can support multiple properties with the same key.
   */
  public final Boolean supportsMultiProperties;
  
  /**
   * Determines if a Vertex can be removed from the Graph.
   */
  public final Boolean supportsRemoveVertices;
  
  /**
   * Determines if the Graph implementation uses upsert functionality as opposed to insert functionality for Graph.addVertex(String).
   */
  public final Boolean supportsUpsert;
  
  public VertexFeatures (hydra.langs.tinkerpop.features.ElementFeatures elementFeatures, hydra.langs.tinkerpop.features.VertexPropertyFeatures properties, Boolean supportsAddVertices, Boolean supportsDuplicateMultiProperties, Boolean supportsMetaProperties, Boolean supportsMultiProperties, Boolean supportsRemoveVertices, Boolean supportsUpsert) {
    this.elementFeatures = elementFeatures;
    this.properties = properties;
    this.supportsAddVertices = supportsAddVertices;
    this.supportsDuplicateMultiProperties = supportsDuplicateMultiProperties;
    this.supportsMetaProperties = supportsMetaProperties;
    this.supportsMultiProperties = supportsMultiProperties;
    this.supportsRemoveVertices = supportsRemoveVertices;
    this.supportsUpsert = supportsUpsert;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof VertexFeatures)) {
      return false;
    }
    VertexFeatures o = (VertexFeatures) (other);
    return elementFeatures.equals(o.elementFeatures) && properties.equals(o.properties) && supportsAddVertices.equals(o.supportsAddVertices) && supportsDuplicateMultiProperties.equals(o.supportsDuplicateMultiProperties) && supportsMetaProperties.equals(o.supportsMetaProperties) && supportsMultiProperties.equals(o.supportsMultiProperties) && supportsRemoveVertices.equals(o.supportsRemoveVertices) && supportsUpsert.equals(o.supportsUpsert);
  }
  
  @Override
  public int hashCode() {
    return 2 * elementFeatures.hashCode() + 3 * properties.hashCode() + 5 * supportsAddVertices.hashCode() + 7 * supportsDuplicateMultiProperties.hashCode() + 11 * supportsMetaProperties.hashCode() + 13 * supportsMultiProperties.hashCode() + 17 * supportsRemoveVertices.hashCode() + 19 * supportsUpsert.hashCode();
  }
  
  public VertexFeatures withElementFeatures(hydra.langs.tinkerpop.features.ElementFeatures elementFeatures) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
  
  public VertexFeatures withProperties(hydra.langs.tinkerpop.features.VertexPropertyFeatures properties) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
  
  public VertexFeatures withSupportsAddVertices(Boolean supportsAddVertices) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
  
  public VertexFeatures withSupportsDuplicateMultiProperties(Boolean supportsDuplicateMultiProperties) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
  
  public VertexFeatures withSupportsMetaProperties(Boolean supportsMetaProperties) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
  
  public VertexFeatures withSupportsMultiProperties(Boolean supportsMultiProperties) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
  
  public VertexFeatures withSupportsRemoveVertices(Boolean supportsRemoveVertices) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
  
  public VertexFeatures withSupportsUpsert(Boolean supportsUpsert) {
    return new VertexFeatures(elementFeatures, properties, supportsAddVertices, supportsDuplicateMultiProperties, supportsMetaProperties, supportsMultiProperties, supportsRemoveVertices, supportsUpsert);
  }
}