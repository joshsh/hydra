// Note: this is an automatically generated file. Do not edit.

package hydra.langs.owl.syntax;

import java.io.Serializable;

public class DatatypeRestriction_Constraint implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.DatatypeRestriction.Constraint");
  
  public final hydra.langs.owl.syntax.DatatypeRestriction_ConstrainingFacet constrainingFacet;
  
  public final hydra.langs.rdf.syntax.Literal restrictionValue;
  
  public DatatypeRestriction_Constraint (hydra.langs.owl.syntax.DatatypeRestriction_ConstrainingFacet constrainingFacet, hydra.langs.rdf.syntax.Literal restrictionValue) {
    if (constrainingFacet == null) {
      throw new IllegalArgumentException("null value for 'constrainingFacet' argument");
    }
    if (restrictionValue == null) {
      throw new IllegalArgumentException("null value for 'restrictionValue' argument");
    }
    this.constrainingFacet = constrainingFacet;
    this.restrictionValue = restrictionValue;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DatatypeRestriction_Constraint)) {
      return false;
    }
    DatatypeRestriction_Constraint o = (DatatypeRestriction_Constraint) (other);
    return constrainingFacet.equals(o.constrainingFacet) && restrictionValue.equals(o.restrictionValue);
  }
  
  @Override
  public int hashCode() {
    return 2 * constrainingFacet.hashCode() + 3 * restrictionValue.hashCode();
  }
  
  public DatatypeRestriction_Constraint withConstrainingFacet(hydra.langs.owl.syntax.DatatypeRestriction_ConstrainingFacet constrainingFacet) {
    if (constrainingFacet == null) {
      throw new IllegalArgumentException("null value for 'constrainingFacet' argument");
    }
    return new DatatypeRestriction_Constraint(constrainingFacet, restrictionValue);
  }
  
  public DatatypeRestriction_Constraint withRestrictionValue(hydra.langs.rdf.syntax.Literal restrictionValue) {
    if (restrictionValue == null) {
      throw new IllegalArgumentException("null value for 'restrictionValue' argument");
    }
    return new DatatypeRestriction_Constraint(constrainingFacet, restrictionValue);
  }
}