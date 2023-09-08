package hydra.langs.tinkerpop.features;

import java.io.Serializable;

/**
 * Features that are related to Element objects.
 */
public class ElementFeatures implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/features.ElementFeatures");
  
  /**
   * Determines if an Element allows properties to be added.
   */
  public final Boolean supportsAddProperty;
  
  /**
   * Determines if an Element any Java object is a suitable identifier.
   */
  public final Boolean supportsAnyIds;
  
  /**
   * Determines if an Element has a specific custom object as their internal representation.
   */
  public final Boolean supportsCustomIds;
  
  /**
   * Determines if an Element has numeric identifiers as their internal representation.
   */
  public final Boolean supportsNumericIds;
  
  /**
   * Determines if an Element allows properties to be removed.
   */
  public final Boolean supportsRemoveProperty;
  
  /**
   * Determines if an Element has string identifiers as their internal representation.
   */
  public final Boolean supportsStringIds;
  
  /**
   * Determines if an Element can have a user defined identifier.
   */
  public final Boolean supportsUserSuppliedIds;
  
  /**
   * Determines if an Element has UUID identifiers as their internal representation.
   */
  public final Boolean supportsUuidIds;
  
  public ElementFeatures (Boolean supportsAddProperty, Boolean supportsAnyIds, Boolean supportsCustomIds, Boolean supportsNumericIds, Boolean supportsRemoveProperty, Boolean supportsStringIds, Boolean supportsUserSuppliedIds, Boolean supportsUuidIds) {
    this.supportsAddProperty = supportsAddProperty;
    this.supportsAnyIds = supportsAnyIds;
    this.supportsCustomIds = supportsCustomIds;
    this.supportsNumericIds = supportsNumericIds;
    this.supportsRemoveProperty = supportsRemoveProperty;
    this.supportsStringIds = supportsStringIds;
    this.supportsUserSuppliedIds = supportsUserSuppliedIds;
    this.supportsUuidIds = supportsUuidIds;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ElementFeatures)) {
      return false;
    }
    ElementFeatures o = (ElementFeatures) (other);
    return supportsAddProperty.equals(o.supportsAddProperty) && supportsAnyIds.equals(o.supportsAnyIds) && supportsCustomIds.equals(o.supportsCustomIds) && supportsNumericIds.equals(o.supportsNumericIds) && supportsRemoveProperty.equals(o.supportsRemoveProperty) && supportsStringIds.equals(o.supportsStringIds) && supportsUserSuppliedIds.equals(o.supportsUserSuppliedIds) && supportsUuidIds.equals(o.supportsUuidIds);
  }
  
  @Override
  public int hashCode() {
    return 2 * supportsAddProperty.hashCode() + 3 * supportsAnyIds.hashCode() + 5 * supportsCustomIds.hashCode() + 7 * supportsNumericIds.hashCode() + 11 * supportsRemoveProperty.hashCode() + 13 * supportsStringIds.hashCode() + 17 * supportsUserSuppliedIds.hashCode() + 19 * supportsUuidIds.hashCode();
  }
  
  public ElementFeatures withSupportsAddProperty(Boolean supportsAddProperty) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
  
  public ElementFeatures withSupportsAnyIds(Boolean supportsAnyIds) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
  
  public ElementFeatures withSupportsCustomIds(Boolean supportsCustomIds) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
  
  public ElementFeatures withSupportsNumericIds(Boolean supportsNumericIds) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
  
  public ElementFeatures withSupportsRemoveProperty(Boolean supportsRemoveProperty) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
  
  public ElementFeatures withSupportsStringIds(Boolean supportsStringIds) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
  
  public ElementFeatures withSupportsUserSuppliedIds(Boolean supportsUserSuppliedIds) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
  
  public ElementFeatures withSupportsUuidIds(Boolean supportsUuidIds) {
    return new ElementFeatures(supportsAddProperty, supportsAnyIds, supportsCustomIds, supportsNumericIds, supportsRemoveProperty, supportsStringIds, supportsUserSuppliedIds, supportsUuidIds);
  }
}