// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public class EnumBody_Element implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.EnumBody.Element");
  
  public final java.util.List<hydra.langs.java.syntax.EnumConstant> constants;
  
  public final java.util.List<hydra.langs.java.syntax.ClassBodyDeclaration> bodyDeclarations;
  
  public EnumBody_Element (java.util.List<hydra.langs.java.syntax.EnumConstant> constants, java.util.List<hydra.langs.java.syntax.ClassBodyDeclaration> bodyDeclarations) {
    if (constants == null) {
      throw new IllegalArgumentException("null value for 'constants' argument");
    }
    if (bodyDeclarations == null) {
      throw new IllegalArgumentException("null value for 'bodyDeclarations' argument");
    }
    this.constants = constants;
    this.bodyDeclarations = bodyDeclarations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumBody_Element)) {
      return false;
    }
    EnumBody_Element o = (EnumBody_Element) (other);
    return constants.equals(o.constants) && bodyDeclarations.equals(o.bodyDeclarations);
  }
  
  @Override
  public int hashCode() {
    return 2 * constants.hashCode() + 3 * bodyDeclarations.hashCode();
  }
  
  public EnumBody_Element withConstants(java.util.List<hydra.langs.java.syntax.EnumConstant> constants) {
    if (constants == null) {
      throw new IllegalArgumentException("null value for 'constants' argument");
    }
    return new EnumBody_Element(constants, bodyDeclarations);
  }
  
  public EnumBody_Element withBodyDeclarations(java.util.List<hydra.langs.java.syntax.ClassBodyDeclaration> bodyDeclarations) {
    if (bodyDeclarations == null) {
      throw new IllegalArgumentException("null value for 'bodyDeclarations' argument");
    }
    return new EnumBody_Element(constants, bodyDeclarations);
  }
}