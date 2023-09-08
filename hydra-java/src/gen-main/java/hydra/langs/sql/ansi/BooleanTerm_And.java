package hydra.langs.sql.ansi;

import java.io.Serializable;

public class BooleanTerm_And implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.BooleanTerm.And");
  
  public final hydra.langs.sql.ansi.BooleanTerm lhs;
  
  public final hydra.langs.sql.ansi.BooleanFactor rhs;
  
  public BooleanTerm_And (hydra.langs.sql.ansi.BooleanTerm lhs, hydra.langs.sql.ansi.BooleanFactor rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BooleanTerm_And)) {
      return false;
    }
    BooleanTerm_And o = (BooleanTerm_And) (other);
    return lhs.equals(o.lhs) && rhs.equals(o.rhs);
  }
  
  @Override
  public int hashCode() {
    return 2 * lhs.hashCode() + 3 * rhs.hashCode();
  }
  
  public BooleanTerm_And withLhs(hydra.langs.sql.ansi.BooleanTerm lhs) {
    return new BooleanTerm_And(lhs, rhs);
  }
  
  public BooleanTerm_And withRhs(hydra.langs.sql.ansi.BooleanFactor rhs) {
    return new BooleanTerm_And(lhs, rhs);
  }
}