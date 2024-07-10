// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

public class Pattern_Record implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Pattern.Record");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final java.util.List<hydra.langs.haskell.ast.PatternField> fields;
  
  public Pattern_Record (hydra.langs.haskell.ast.Name name, java.util.List<hydra.langs.haskell.ast.PatternField> fields) {
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
    if (!(other instanceof Pattern_Record)) {
      return false;
    }
    Pattern_Record o = (Pattern_Record) (other);
    return name.equals(o.name) && fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * fields.hashCode();
  }
  
  public Pattern_Record withName(hydra.langs.haskell.ast.Name name) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new Pattern_Record(name, fields);
  }
  
  public Pattern_Record withFields(java.util.List<hydra.langs.haskell.ast.PatternField> fields) {
    if (fields == null) {
      throw new IllegalArgumentException("null value for 'fields' argument");
    }
    return new Pattern_Record(name, fields);
  }
}