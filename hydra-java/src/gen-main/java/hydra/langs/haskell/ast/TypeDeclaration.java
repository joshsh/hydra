package hydra.langs.haskell.ast;

import java.io.Serializable;

public class TypeDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.TypeDeclaration");
  
  public final hydra.langs.haskell.ast.DeclarationHead name;
  
  public final hydra.langs.haskell.ast.Type type;
  
  public TypeDeclaration (hydra.langs.haskell.ast.DeclarationHead name, hydra.langs.haskell.ast.Type type) {
    this.name = name;
    this.type = type;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeDeclaration)) {
      return false;
    }
    TypeDeclaration o = (TypeDeclaration) (other);
    return name.equals(o.name) && type.equals(o.type);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * type.hashCode();
  }
  
  public TypeDeclaration withName(hydra.langs.haskell.ast.DeclarationHead name) {
    return new TypeDeclaration(name, type);
  }
  
  public TypeDeclaration withType(hydra.langs.haskell.ast.Type type) {
    return new TypeDeclaration(name, type);
  }
}