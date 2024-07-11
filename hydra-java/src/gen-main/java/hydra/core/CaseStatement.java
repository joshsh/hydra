// Note: this is an automatically generated file. Do not edit.

package hydra.core;

import hydra.util.Opt;

import java.io.Serializable;

/**
 * A union elimination; a case statement
 */
public class CaseStatement<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.CaseStatement");
  
  public final hydra.core.Name typeName;
  
  public final Opt<Term<A>> default_;
  
  public final java.util.List<hydra.core.Field<A>> cases;
  
  public CaseStatement (hydra.core.Name typeName, Opt<Term<A>> default_, java.util.List<hydra.core.Field<A>> cases) {
    if (typeName == null) {
      throw new IllegalArgumentException("null value for 'typeName' argument");
    }
    if (default_ == null) {
      throw new IllegalArgumentException("null value for 'default' argument");
    }
    if (cases == null) {
      throw new IllegalArgumentException("null value for 'cases' argument");
    }
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
    if (typeName == null) {
      throw new IllegalArgumentException("null value for 'typeName' argument");
    }
    return new CaseStatement(typeName, default_, cases);
  }
  
  public CaseStatement withDefault(Opt<Term<A>> default_) {
    if (default_ == null) {
      throw new IllegalArgumentException("null value for 'default' argument");
    }
    return new CaseStatement(typeName, default_, cases);
  }
  
  public CaseStatement withCases(java.util.List<hydra.core.Field<A>> cases) {
    if (cases == null) {
      throw new IllegalArgumentException("null value for 'cases' argument");
    }
    return new CaseStatement(typeName, default_, cases);
  }
}
