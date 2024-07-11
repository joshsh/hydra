// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A data constructor together with any comments
 */
public class ConstructorWithComments implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.ConstructorWithComments");
  
  public final hydra.langs.haskell.ast.Constructor body;
  
  public final hydra.util.Opt<String> comments;
  
  public ConstructorWithComments (hydra.langs.haskell.ast.Constructor body, hydra.util.Opt<String> comments) {
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
    if (comments == null) {
      throw new IllegalArgumentException("null value for 'comments' argument");
    }
    this.body = body;
    this.comments = comments;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ConstructorWithComments)) {
      return false;
    }
    ConstructorWithComments o = (ConstructorWithComments) (other);
    return body.equals(o.body) && comments.equals(o.comments);
  }
  
  @Override
  public int hashCode() {
    return 2 * body.hashCode() + 3 * comments.hashCode();
  }
  
  public ConstructorWithComments withBody(hydra.langs.haskell.ast.Constructor body) {
    if (body == null) {
      throw new IllegalArgumentException("null value for 'body' argument");
    }
    return new ConstructorWithComments(body, comments);
  }
  
  public ConstructorWithComments withComments(hydra.util.Opt<String> comments) {
    if (comments == null) {
      throw new IllegalArgumentException("null value for 'comments' argument");
    }
    return new ConstructorWithComments(body, comments);
  }
}