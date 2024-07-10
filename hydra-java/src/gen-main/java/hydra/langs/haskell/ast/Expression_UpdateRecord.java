// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * An update record expression
 */
public class Expression_UpdateRecord implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Expression.UpdateRecord");
  
  public final hydra.langs.haskell.ast.Expression inner;
  
  public final java.util.List<hydra.langs.haskell.ast.FieldUpdate> fields;
  
  public Expression_UpdateRecord (hydra.langs.haskell.ast.Expression inner, java.util.List<hydra.langs.haskell.ast.FieldUpdate> fields) {
    if (inner == null) {
      throw new IllegalArgumentException("null value for 'inner' argument");
    }
    if (fields == null) {
      throw new IllegalArgumentException("null value for 'fields' argument");
    }
    this.inner = inner;
    this.fields = fields;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Expression_UpdateRecord)) {
      return false;
    }
    Expression_UpdateRecord o = (Expression_UpdateRecord) (other);
    return inner.equals(o.inner) && fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * inner.hashCode() + 3 * fields.hashCode();
  }
  
  public Expression_UpdateRecord withInner(hydra.langs.haskell.ast.Expression inner) {
    if (inner == null) {
      throw new IllegalArgumentException("null value for 'inner' argument");
    }
    return new Expression_UpdateRecord(inner, fields);
  }
  
  public Expression_UpdateRecord withFields(java.util.List<hydra.langs.haskell.ast.FieldUpdate> fields) {
    if (fields == null) {
      throw new IllegalArgumentException("null value for 'fields' argument");
    }
    return new Expression_UpdateRecord(inner, fields);
  }
}