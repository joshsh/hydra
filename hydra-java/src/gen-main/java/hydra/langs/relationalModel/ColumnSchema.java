package hydra.langs.relationalModel;

import java.io.Serializable;

/**
 * An abstract specification of the domain represented by a column in a relation; a role
 */
public class ColumnSchema<T> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/relationalModel.ColumnSchema");
  
  /**
   * A unique name for the column
   */
  public final hydra.langs.relationalModel.ColumnName name;
  
  /**
   * The domain (type) of the column
   */
  public final T domain;
  
  /**
   * Whether this column represents the primary key of its relation
   */
  public final Boolean isPrimaryKey;
  
  public ColumnSchema (hydra.langs.relationalModel.ColumnName name, T domain, Boolean isPrimaryKey) {
    this.name = name;
    this.domain = domain;
    this.isPrimaryKey = isPrimaryKey;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ColumnSchema)) {
      return false;
    }
    ColumnSchema o = (ColumnSchema) (other);
    return name.equals(o.name) && domain.equals(o.domain) && isPrimaryKey.equals(o.isPrimaryKey);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * domain.hashCode() + 5 * isPrimaryKey.hashCode();
  }
  
  public ColumnSchema withName(hydra.langs.relationalModel.ColumnName name) {
    return new ColumnSchema(name, domain, isPrimaryKey);
  }
  
  public ColumnSchema withDomain(T domain) {
    return new ColumnSchema(name, domain, isPrimaryKey);
  }
  
  public ColumnSchema withIsPrimaryKey(Boolean isPrimaryKey) {
    return new ColumnSchema(name, domain, isPrimaryKey);
  }
}