// Note: this is an automatically generated file. Do not edit.

package hydra.core;

import java.io.Serializable;

/**
 * A labeled record or union type
 */
public class RowType<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.RowType");
  
  /**
   * The name of the row type, which must correspond to the name of a Type element
   */
  public final hydra.core.Name typeName;
  
  /**
   * Optionally, the name of another row type which this one extends. If/when field order is preserved, the inherited fields of the extended type precede those of the extension.
   */
  public final java.util.Optional<hydra.core.Name> extends_;
  
  /**
   * The fields of this row type, excluding any inherited fields
   */
  public final java.util.List<hydra.core.FieldType<A>> fields;
  
  public RowType (hydra.core.Name typeName, java.util.Optional<hydra.core.Name> extends_, java.util.List<hydra.core.FieldType<A>> fields) {
    if (typeName == null) {
      throw new IllegalArgumentException("null value for 'typeName' argument");
    }
    if (extends_ == null) {
      throw new IllegalArgumentException("null value for 'extends' argument");
    }
    if (fields == null) {
      throw new IllegalArgumentException("null value for 'fields' argument");
    }
    this.typeName = typeName;
    this.extends_ = extends_;
    this.fields = fields;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RowType)) {
      return false;
    }
    RowType o = (RowType) (other);
    return typeName.equals(o.typeName) && extends_.equals(o.extends_) && fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeName.hashCode() + 3 * extends_.hashCode() + 5 * fields.hashCode();
  }
  
  public RowType withTypeName(hydra.core.Name typeName) {
    if (typeName == null) {
      throw new IllegalArgumentException("null value for 'typeName' argument");
    }
    return new RowType(typeName, extends_, fields);
  }
  
  public RowType withExtends(java.util.Optional<hydra.core.Name> extends_) {
    if (extends_ == null) {
      throw new IllegalArgumentException("null value for 'extends' argument");
    }
    return new RowType(typeName, extends_, fields);
  }
  
  public RowType withFields(java.util.List<hydra.core.FieldType<A>> fields) {
    if (fields == null) {
      throw new IllegalArgumentException("null value for 'fields' argument");
    }
    return new RowType(typeName, extends_, fields);
  }
}