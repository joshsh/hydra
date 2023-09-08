package hydra.langs.haskell.ast;

import java.io.Serializable;

public class ModuleHead implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.ModuleHead");
  
  public final java.util.Optional<String> comments;
  
  public final hydra.langs.haskell.ast.ModuleName name;
  
  public final java.util.List<hydra.langs.haskell.ast.Export> exports;
  
  public ModuleHead (java.util.Optional<String> comments, hydra.langs.haskell.ast.ModuleName name, java.util.List<hydra.langs.haskell.ast.Export> exports) {
    this.comments = comments;
    this.name = name;
    this.exports = exports;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ModuleHead)) {
      return false;
    }
    ModuleHead o = (ModuleHead) (other);
    return comments.equals(o.comments) && name.equals(o.name) && exports.equals(o.exports);
  }
  
  @Override
  public int hashCode() {
    return 2 * comments.hashCode() + 3 * name.hashCode() + 5 * exports.hashCode();
  }
  
  public ModuleHead withComments(java.util.Optional<String> comments) {
    return new ModuleHead(comments, name, exports);
  }
  
  public ModuleHead withName(hydra.langs.haskell.ast.ModuleName name) {
    return new ModuleHead(comments, name, exports);
  }
  
  public ModuleHead withExports(java.util.List<hydra.langs.haskell.ast.Export> exports) {
    return new ModuleHead(comments, name, exports);
  }
}