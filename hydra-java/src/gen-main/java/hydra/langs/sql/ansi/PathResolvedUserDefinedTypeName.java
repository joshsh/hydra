package hydra.langs.sql.ansi;

import java.io.Serializable;

public class PathResolvedUserDefinedTypeName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.PathResolvedUserDefinedTypeName");
  
  public final String value;
  
  public PathResolvedUserDefinedTypeName (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PathResolvedUserDefinedTypeName)) {
      return false;
    }
    PathResolvedUserDefinedTypeName o = (PathResolvedUserDefinedTypeName) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}