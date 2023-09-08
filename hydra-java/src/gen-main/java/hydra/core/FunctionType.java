package hydra.core;

import java.io.Serializable;

/**
 * A function type, also known as an arrow type
 */
public class FunctionType<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.FunctionType");
  
  public final hydra.core.Type<A> domain;
  
  public final hydra.core.Type<A> codomain;
  
  public FunctionType (hydra.core.Type<A> domain, hydra.core.Type<A> codomain) {
    this.domain = domain;
    this.codomain = codomain;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FunctionType)) {
      return false;
    }
    FunctionType o = (FunctionType) (other);
    return domain.equals(o.domain) && codomain.equals(o.codomain);
  }
  
  @Override
  public int hashCode() {
    return 2 * domain.hashCode() + 3 * codomain.hashCode();
  }
  
  public FunctionType withDomain(hydra.core.Type<A> domain) {
    return new FunctionType(domain, codomain);
  }
  
  public FunctionType withCodomain(hydra.core.Type<A> codomain) {
    return new FunctionType(domain, codomain);
  }
}