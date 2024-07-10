// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.features;

import java.io.Serializable;

/**
 * Features that are related to Vertex Property objects.
 */
public class VertexPropertyFeatures implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/features.VertexPropertyFeatures");
  
  public final hydra.langs.tinkerpop.features.DataTypeFeatures dataTypeFeatures;
  
  public final hydra.langs.tinkerpop.features.PropertyFeatures propertyFeatures;
  
  public final hydra.langs.tinkerpop.features.ElementFeatures elementFeatures;
  
  /**
   * Determines if a VertexProperty allows properties to be removed.
   */
  public final Boolean supportsRemove;
  
  public VertexPropertyFeatures (hydra.langs.tinkerpop.features.DataTypeFeatures dataTypeFeatures, hydra.langs.tinkerpop.features.PropertyFeatures propertyFeatures, hydra.langs.tinkerpop.features.ElementFeatures elementFeatures, Boolean supportsRemove) {
    if (dataTypeFeatures == null) {
      throw new IllegalArgumentException("null value for 'dataTypeFeatures' argument");
    }
    if (propertyFeatures == null) {
      throw new IllegalArgumentException("null value for 'propertyFeatures' argument");
    }
    if (elementFeatures == null) {
      throw new IllegalArgumentException("null value for 'elementFeatures' argument");
    }
    if (supportsRemove == null) {
      throw new IllegalArgumentException("null value for 'supportsRemove' argument");
    }
    this.dataTypeFeatures = dataTypeFeatures;
    this.propertyFeatures = propertyFeatures;
    this.elementFeatures = elementFeatures;
    this.supportsRemove = supportsRemove;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof VertexPropertyFeatures)) {
      return false;
    }
    VertexPropertyFeatures o = (VertexPropertyFeatures) (other);
    return dataTypeFeatures.equals(o.dataTypeFeatures) && propertyFeatures.equals(o.propertyFeatures) && elementFeatures.equals(o.elementFeatures) && supportsRemove.equals(o.supportsRemove);
  }
  
  @Override
  public int hashCode() {
    return 2 * dataTypeFeatures.hashCode() + 3 * propertyFeatures.hashCode() + 5 * elementFeatures.hashCode() + 7 * supportsRemove.hashCode();
  }
  
  public VertexPropertyFeatures withDataTypeFeatures(hydra.langs.tinkerpop.features.DataTypeFeatures dataTypeFeatures) {
    if (dataTypeFeatures == null) {
      throw new IllegalArgumentException("null value for 'dataTypeFeatures' argument");
    }
    return new VertexPropertyFeatures(dataTypeFeatures, propertyFeatures, elementFeatures, supportsRemove);
  }
  
  public VertexPropertyFeatures withPropertyFeatures(hydra.langs.tinkerpop.features.PropertyFeatures propertyFeatures) {
    if (propertyFeatures == null) {
      throw new IllegalArgumentException("null value for 'propertyFeatures' argument");
    }
    return new VertexPropertyFeatures(dataTypeFeatures, propertyFeatures, elementFeatures, supportsRemove);
  }
  
  public VertexPropertyFeatures withElementFeatures(hydra.langs.tinkerpop.features.ElementFeatures elementFeatures) {
    if (elementFeatures == null) {
      throw new IllegalArgumentException("null value for 'elementFeatures' argument");
    }
    return new VertexPropertyFeatures(dataTypeFeatures, propertyFeatures, elementFeatures, supportsRemove);
  }
  
  public VertexPropertyFeatures withSupportsRemove(Boolean supportsRemove) {
    if (supportsRemove == null) {
      throw new IllegalArgumentException("null value for 'supportsRemove' argument");
    }
    return new VertexPropertyFeatures(dataTypeFeatures, propertyFeatures, elementFeatures, supportsRemove);
  }
}