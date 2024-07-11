// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A field together with any comments
 */
public class FieldWithComments implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.FieldWithComments");
  
  public final hydra.langs.haskell.ast.Field field;
  
  public final hydra.util.Opt<String> comments;
  
  public FieldWithComments (hydra.langs.haskell.ast.Field field, hydra.util.Opt<String> comments) {
    if (field == null) {
      throw new IllegalArgumentException("null value for 'field' argument");
    }
    if (comments == null) {
      throw new IllegalArgumentException("null value for 'comments' argument");
    }
    this.field = field;
    this.comments = comments;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FieldWithComments)) {
      return false;
    }
    FieldWithComments o = (FieldWithComments) (other);
    return field.equals(o.field) && comments.equals(o.comments);
  }
  
  @Override
  public int hashCode() {
    return 2 * field.hashCode() + 3 * comments.hashCode();
  }
  
  public FieldWithComments withField(hydra.langs.haskell.ast.Field field) {
    if (field == null) {
      throw new IllegalArgumentException("null value for 'field' argument");
    }
    return new FieldWithComments(field, comments);
  }
  
  public FieldWithComments withComments(hydra.util.Opt<String> comments) {
    if (comments == null) {
      throw new IllegalArgumentException("null value for 'comments' argument");
    }
    return new FieldWithComments(field, comments);
  }
}