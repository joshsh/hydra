// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class VariableDeclaratorId implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/java/syntax.VariableDeclaratorId");
  
  public static final hydra.core.Name FIELD_NAME_IDENTIFIER = new hydra.core.Name("identifier");
  
  public static final hydra.core.Name FIELD_NAME_DIMS = new hydra.core.Name("dims");
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public final hydra.util.Opt<hydra.langs.java.syntax.Dims> dims;
  
  public VariableDeclaratorId (hydra.langs.java.syntax.Identifier identifier, hydra.util.Opt<hydra.langs.java.syntax.Dims> dims) {
    java.util.Objects.requireNonNull((identifier));
    java.util.Objects.requireNonNull((dims));
    this.identifier = identifier;
    this.dims = dims;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof VariableDeclaratorId)) {
      return false;
    }
    VariableDeclaratorId o = (VariableDeclaratorId) (other);
    return identifier.equals(o.identifier) && dims.equals(o.dims);
  }
  
  @Override
  public int hashCode() {
    return 2 * identifier.hashCode() + 3 * dims.hashCode();
  }
  
  public VariableDeclaratorId withIdentifier(hydra.langs.java.syntax.Identifier identifier) {
    java.util.Objects.requireNonNull((identifier));
    return new VariableDeclaratorId(identifier, dims);
  }
  
  public VariableDeclaratorId withDims(hydra.util.Opt<hydra.langs.java.syntax.Dims> dims) {
    java.util.Objects.requireNonNull((dims));
    return new VariableDeclaratorId(identifier, dims);
  }
}