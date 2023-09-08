package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A field (name/type pair)
 */
public class Field implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.Field");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final hydra.langs.haskell.ast.Type type;
  
  public Field (hydra.langs.haskell.ast.Name name, hydra.langs.haskell.ast.Type type) {
    this.name = name;
    this.type = type;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Field)) {
      return false;
    }
    Field o = (Field) (other);
    return name.equals(o.name) && type.equals(o.type);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * type.hashCode();
  }
  
  public Field withName(hydra.langs.haskell.ast.Name name) {
    return new Field(name, type);
  }
  
  public Field withType(hydra.langs.haskell.ast.Type type) {
    return new Field(name, type);
  }
}