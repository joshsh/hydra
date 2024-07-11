// Note: this is an automatically generated file. Do not edit.

package hydra.langs.sql.ansi;

import java.io.Serializable;

public class PredefinedType_NationalString implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.PredefinedType.NationalString");
  
  public final hydra.langs.sql.ansi.NationalCharacterStringType type;
  
  public final hydra.util.Opt<hydra.langs.sql.ansi.CollateClause> collate;
  
  public PredefinedType_NationalString (hydra.langs.sql.ansi.NationalCharacterStringType type, hydra.util.Opt<hydra.langs.sql.ansi.CollateClause> collate) {
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    if (collate == null) {
      throw new IllegalArgumentException("null value for 'collate' argument");
    }
    this.type = type;
    this.collate = collate;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PredefinedType_NationalString)) {
      return false;
    }
    PredefinedType_NationalString o = (PredefinedType_NationalString) (other);
    return type.equals(o.type) && collate.equals(o.collate);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * collate.hashCode();
  }
  
  public PredefinedType_NationalString withType(hydra.langs.sql.ansi.NationalCharacterStringType type) {
    if (type == null) {
      throw new IllegalArgumentException("null value for 'type' argument");
    }
    return new PredefinedType_NationalString(type, collate);
  }
  
  public PredefinedType_NationalString withCollate(hydra.util.Opt<hydra.langs.sql.ansi.CollateClause> collate) {
    if (collate == null) {
      throw new IllegalArgumentException("null value for 'collate' argument");
    }
    return new PredefinedType_NationalString(type, collate);
  }
}