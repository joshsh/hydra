package hydra.langs.sql.ansi;

import java.io.Serializable;

public class ColumnNameList implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ColumnNameList");
  
  public final hydra.langs.sql.ansi.ColumnName first;
  
  public final java.util.List<hydra.langs.sql.ansi.ColumnName> rest;
  
  public ColumnNameList (hydra.langs.sql.ansi.ColumnName first, java.util.List<hydra.langs.sql.ansi.ColumnName> rest) {
    this.first = first;
    this.rest = rest;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnNameList)) {
      return false;
    }
    ColumnNameList o = (ColumnNameList) (other);
    return first.equals(o.first) && rest.equals(o.rest);
  }
  
  @Override
  public int hashCode() {
    return 2 * first.hashCode() + 3 * rest.hashCode();
  }
  
  public ColumnNameList withFirst(hydra.langs.sql.ansi.ColumnName first) {
    return new ColumnNameList(first, rest);
  }
  
  public ColumnNameList withRest(java.util.List<hydra.langs.sql.ansi.ColumnName> rest) {
    return new ColumnNameList(first, rest);
  }
}