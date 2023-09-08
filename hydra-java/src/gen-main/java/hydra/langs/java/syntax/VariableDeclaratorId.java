package hydra.langs.java.syntax;

import java.io.Serializable;

public class VariableDeclaratorId implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.VariableDeclaratorId");
  
  public final hydra.langs.java.syntax.Identifier identifier;
  
  public final java.util.Optional<hydra.langs.java.syntax.Dims> dims;
  
  public VariableDeclaratorId (hydra.langs.java.syntax.Identifier identifier, java.util.Optional<hydra.langs.java.syntax.Dims> dims) {
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
    return new VariableDeclaratorId(identifier, dims);
  }
  
  public VariableDeclaratorId withDims(java.util.Optional<hydra.langs.java.syntax.Dims> dims) {
    return new VariableDeclaratorId(identifier, dims);
  }
}