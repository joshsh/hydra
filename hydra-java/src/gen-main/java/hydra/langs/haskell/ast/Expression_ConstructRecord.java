// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A record constructor expression
 */
public class Expression_ConstructRecord implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/haskell/ast.Expression.ConstructRecord");
  
  public static final hydra.core.Name FIELD_NAME_NAME = new hydra.core.Name("name");
  
  public static final hydra.core.Name FIELD_NAME_FIELDS = new hydra.core.Name("fields");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final java.util.List<hydra.langs.haskell.ast.FieldUpdate> fields;
  
  public Expression_ConstructRecord (hydra.langs.haskell.ast.Name name, java.util.List<hydra.langs.haskell.ast.FieldUpdate> fields) {
    java.util.Objects.requireNonNull((name));
    java.util.Objects.requireNonNull((fields));
    this.name = name;
    this.fields = fields;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Expression_ConstructRecord)) {
      return false;
    }
    Expression_ConstructRecord o = (Expression_ConstructRecord) (other);
    return name.equals(o.name) && fields.equals(o.fields);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * fields.hashCode();
  }
  
  public Expression_ConstructRecord withName(hydra.langs.haskell.ast.Name name) {
    java.util.Objects.requireNonNull((name));
    return new Expression_ConstructRecord(name, fields);
  }
  
  public Expression_ConstructRecord withFields(java.util.List<hydra.langs.haskell.ast.FieldUpdate> fields) {
    java.util.Objects.requireNonNull((fields));
    return new Expression_ConstructRecord(name, fields);
  }
}