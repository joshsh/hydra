package hydra.langs.sql.ansi;

import java.io.Serializable;

public class TableContentsSource_Subtable implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.TableContentsSource.Subtable");
  
  public final hydra.langs.sql.ansi.PathResolvedUserDefinedTypeName type;
  
  public final java.util.Optional<hydra.langs.sql.ansi.SubtableClause> subtable;
  
  public final java.util.Optional<hydra.langs.sql.ansi.TableElementList> elements;
  
  public TableContentsSource_Subtable (hydra.langs.sql.ansi.PathResolvedUserDefinedTypeName type, java.util.Optional<hydra.langs.sql.ansi.SubtableClause> subtable, java.util.Optional<hydra.langs.sql.ansi.TableElementList> elements) {
    this.type = type;
    this.subtable = subtable;
    this.elements = elements;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TableContentsSource_Subtable)) {
      return false;
    }
    TableContentsSource_Subtable o = (TableContentsSource_Subtable) (other);
    return type.equals(o.type) && subtable.equals(o.subtable) && elements.equals(o.elements);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * subtable.hashCode() + 5 * elements.hashCode();
  }
  
  public TableContentsSource_Subtable withType(hydra.langs.sql.ansi.PathResolvedUserDefinedTypeName type) {
    return new TableContentsSource_Subtable(type, subtable, elements);
  }
  
  public TableContentsSource_Subtable withSubtable(java.util.Optional<hydra.langs.sql.ansi.SubtableClause> subtable) {
    return new TableContentsSource_Subtable(type, subtable, elements);
  }
  
  public TableContentsSource_Subtable withElements(java.util.Optional<hydra.langs.sql.ansi.TableElementList> elements) {
    return new TableContentsSource_Subtable(type, subtable, elements);
  }
}