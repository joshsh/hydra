package hydra.langs.java.syntax;

import java.io.Serializable;

public class TypeDeclarationWithComments implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TypeDeclarationWithComments");
  
  public final hydra.langs.java.syntax.TypeDeclaration value;
  
  public final java.util.Optional<String> comments;
  
  public TypeDeclarationWithComments (hydra.langs.java.syntax.TypeDeclaration value, java.util.Optional<String> comments) {
    this.value = value;
    this.comments = comments;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeDeclarationWithComments)) {
      return false;
    }
    TypeDeclarationWithComments o = (TypeDeclarationWithComments) (other);
    return value.equals(o.value) && comments.equals(o.comments);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode() + 3 * comments.hashCode();
  }
  
  public TypeDeclarationWithComments withValue(hydra.langs.java.syntax.TypeDeclaration value) {
    return new TypeDeclarationWithComments(value, comments);
  }
  
  public TypeDeclarationWithComments withComments(java.util.Optional<String> comments) {
    return new TypeDeclarationWithComments(value, comments);
  }
}