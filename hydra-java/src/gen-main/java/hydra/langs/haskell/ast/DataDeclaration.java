package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * A data type declaration
 */
public class DataDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.DataDeclaration");
  
  public final hydra.langs.haskell.ast.DataDeclaration_Keyword keyword;
  
  public final java.util.List<hydra.langs.haskell.ast.Assertion> context;
  
  public final hydra.langs.haskell.ast.DeclarationHead head;
  
  public final java.util.List<hydra.langs.haskell.ast.ConstructorWithComments> constructors;
  
  public final java.util.List<hydra.langs.haskell.ast.Deriving> deriving;
  
  public DataDeclaration (hydra.langs.haskell.ast.DataDeclaration_Keyword keyword, java.util.List<hydra.langs.haskell.ast.Assertion> context, hydra.langs.haskell.ast.DeclarationHead head, java.util.List<hydra.langs.haskell.ast.ConstructorWithComments> constructors, java.util.List<hydra.langs.haskell.ast.Deriving> deriving) {
    this.keyword = keyword;
    this.context = context;
    this.head = head;
    this.constructors = constructors;
    this.deriving = deriving;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DataDeclaration)) {
      return false;
    }
    DataDeclaration o = (DataDeclaration) (other);
    return keyword.equals(o.keyword) && context.equals(o.context) && head.equals(o.head) && constructors.equals(o.constructors) && deriving.equals(o.deriving);
  }
  
  @Override
  public int hashCode() {
    return 2 * keyword.hashCode() + 3 * context.hashCode() + 5 * head.hashCode() + 7 * constructors.hashCode() + 11 * deriving.hashCode();
  }
  
  public DataDeclaration withKeyword(hydra.langs.haskell.ast.DataDeclaration_Keyword keyword) {
    return new DataDeclaration(keyword, context, head, constructors, deriving);
  }
  
  public DataDeclaration withContext(java.util.List<hydra.langs.haskell.ast.Assertion> context) {
    return new DataDeclaration(keyword, context, head, constructors, deriving);
  }
  
  public DataDeclaration withHead(hydra.langs.haskell.ast.DeclarationHead head) {
    return new DataDeclaration(keyword, context, head, constructors, deriving);
  }
  
  public DataDeclaration withConstructors(java.util.List<hydra.langs.haskell.ast.ConstructorWithComments> constructors) {
    return new DataDeclaration(keyword, context, head, constructors, deriving);
  }
  
  public DataDeclaration withDeriving(java.util.List<hydra.langs.haskell.ast.Deriving> deriving) {
    return new DataDeclaration(keyword, context, head, constructors, deriving);
  }
}