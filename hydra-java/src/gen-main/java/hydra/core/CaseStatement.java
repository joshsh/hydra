package hydra.core;

import java.io.Serializable;

/**
 * A union elimination; a case statement
 */
public class CaseStatement<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.CaseStatement");
  
  public final hydra.core.Name typeName;
  
  public final java.util.Optional<hydra.core.Term<A>> default_;
  
  public final java.util.List<hydra.core.Field<A>> cases;
  
  public CaseStatement (hydra.core.Name typeName, java.util.Optional<hydra.core.Term<A>> default_, java.util.List<hydra.core.Field<A>> cases) {
    this.typeName = typeName;
    this.default_ = default_;
    this.cases = cases;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CaseStatement)) {
      return false;
    }
    CaseStatement o = (CaseStatement) (other);
    return typeName.equals(o.typeName) && default_.equals(o.default_) && cases.equals(o.cases);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeName.hashCode() + 3 * default_.hashCode() + 5 * cases.hashCode();
  }
  
  public CaseStatement withTypeName(hydra.core.Name typeName) {
    return new CaseStatement(typeName, default_, cases);
  }
  
  public CaseStatement withDefault(java.util.Optional<hydra.core.Term<A>> default_) {
    return new CaseStatement(typeName, default_, cases);
  }
  
  public CaseStatement withCases(java.util.List<hydra.core.Field<A>> cases) {
    return new CaseStatement(typeName, default_, cases);
  }
}