package hydra.langs.haskell.ast;

import java.io.Serializable;

public class QualifiedName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.QualifiedName");
  
  public final java.util.List<hydra.langs.haskell.ast.NamePart> qualifiers;
  
  public final hydra.langs.haskell.ast.NamePart unqualified;
  
  public QualifiedName (java.util.List<hydra.langs.haskell.ast.NamePart> qualifiers, hydra.langs.haskell.ast.NamePart unqualified) {
    this.qualifiers = qualifiers;
    this.unqualified = unqualified;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof QualifiedName)) {
      return false;
    }
    QualifiedName o = (QualifiedName) (other);
    return qualifiers.equals(o.qualifiers) && unqualified.equals(o.unqualified);
  }
  
  @Override
  public int hashCode() {
    return 2 * qualifiers.hashCode() + 3 * unqualified.hashCode();
  }
  
  public QualifiedName withQualifiers(java.util.List<hydra.langs.haskell.ast.NamePart> qualifiers) {
    return new QualifiedName(qualifiers, unqualified);
  }
  
  public QualifiedName withUnqualified(hydra.langs.haskell.ast.NamePart unqualified) {
    return new QualifiedName(qualifiers, unqualified);
  }
}