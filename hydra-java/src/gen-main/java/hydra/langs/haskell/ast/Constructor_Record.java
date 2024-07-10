// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A record-style data constructor
 */
public class Constructor_Record implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Constructor.Record");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final java.util.List<hydra.langs.haskell.ast.FieldWithComments> fields;
  
  public Constructor_Record (hydra.langs.haskell.ast.Name name, java.util.List<hydra.langs.haskell.ast.FieldWithComments> fields) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    if (fields == null) {
      throw new IllegalArgumentException("null value for 'fields' argument");
    }
    this.name = name;
    this.fields = fields;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Constructor_Record)) {
      return false;
    }
    Constructor_Record o = (Constructor_Record) (other);
    return name.equals(o.name) && fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * fields.hashCode();
  }
  
  public Constructor_Record withName(hydra.langs.haskell.ast.Name name) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new Constructor_Record(name, fields);
  }
  
  public Constructor_Record withFields(java.util.List<hydra.langs.haskell.ast.FieldWithComments> fields) {
    if (fields == null) {
      throw new IllegalArgumentException("null value for 'fields' argument");
    }
    return new Constructor_Record(name, fields);
  }
}