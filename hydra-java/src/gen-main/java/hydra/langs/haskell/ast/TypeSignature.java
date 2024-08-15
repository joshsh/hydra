// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

public class TypeSignature implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/haskell/ast.TypeSignature");
  
  public static final hydra.core.Name FIELD_NAME_NAME = new hydra.core.Name("name");
  
  public static final hydra.core.Name FIELD_NAME_TYPE = new hydra.core.Name("type");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final hydra.langs.haskell.ast.Type type;
  
  public TypeSignature (hydra.langs.haskell.ast.Name name, hydra.langs.haskell.ast.Type type) {
    java.util.Objects.requireNonNull((name));
    java.util.Objects.requireNonNull((type));
    this.name = name;
    this.type = type;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeSignature)) {
      return false;
    }
    TypeSignature o = (TypeSignature) (other);
    return name.equals(o.name) && type.equals(o.type);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * type.hashCode();
  }
  
  public TypeSignature withName(hydra.langs.haskell.ast.Name name) {
    java.util.Objects.requireNonNull((name));
    return new TypeSignature(name, type);
  }
  
  public TypeSignature withType(hydra.langs.haskell.ast.Type type) {
    java.util.Objects.requireNonNull((type));
    return new TypeSignature(name, type);
  }
}