package hydra.langs.kusto.kql;

import java.io.Serializable;

public class SortBy implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/kusto/kql.SortBy");
  
  public final hydra.langs.kusto.kql.ColumnName column;
  
  public final java.util.Optional<hydra.langs.kusto.kql.Order> order;
  
  public SortBy (hydra.langs.kusto.kql.ColumnName column, java.util.Optional<hydra.langs.kusto.kql.Order> order) {
    this.column = column;
    this.order = order;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SortBy)) {
      return false;
    }
    SortBy o = (SortBy) (other);
    return column.equals(o.column) && order.equals(o.order);
  }
  
  @Override
  public int hashCode() {
    return 2 * column.hashCode() + 3 * order.hashCode();
  }
  
  public SortBy withColumn(hydra.langs.kusto.kql.ColumnName column) {
    return new SortBy(column, order);
  }
  
  public SortBy withOrder(java.util.Optional<hydra.langs.kusto.kql.Order> order) {
    return new SortBy(column, order);
  }
}