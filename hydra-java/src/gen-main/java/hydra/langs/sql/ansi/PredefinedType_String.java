package hydra.langs.sql.ansi;

import java.io.Serializable;

public class PredefinedType_String implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.PredefinedType.String");
  
  public final hydra.langs.sql.ansi.CharacterStringType type;
  
  public final java.util.Optional<hydra.langs.sql.ansi.CharacterSetSpecification> characters;
  
  public final java.util.Optional<hydra.langs.sql.ansi.CollateClause> collate;
  
  public PredefinedType_String (hydra.langs.sql.ansi.CharacterStringType type, java.util.Optional<hydra.langs.sql.ansi.CharacterSetSpecification> characters, java.util.Optional<hydra.langs.sql.ansi.CollateClause> collate) {
    this.type = type;
    this.characters = characters;
    this.collate = collate;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PredefinedType_String)) {
      return false;
    }
    PredefinedType_String o = (PredefinedType_String) (other);
    return type.equals(o.type) && characters.equals(o.characters) && collate.equals(o.collate);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * characters.hashCode() + 5 * collate.hashCode();
  }
  
  public PredefinedType_String withType(hydra.langs.sql.ansi.CharacterStringType type) {
    return new PredefinedType_String(type, characters, collate);
  }
  
  public PredefinedType_String withCharacters(java.util.Optional<hydra.langs.sql.ansi.CharacterSetSpecification> characters) {
    return new PredefinedType_String(type, characters, collate);
  }
  
  public PredefinedType_String withCollate(java.util.Optional<hydra.langs.sql.ansi.CollateClause> collate) {
    return new PredefinedType_String(type, characters, collate);
  }
}