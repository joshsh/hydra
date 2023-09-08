package hydra.langs.java.syntax;

import java.io.Serializable;

public class ClassType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ClassType");
  
  public final java.util.List<hydra.langs.java.syntax.Annotation> annotations;
  
  public final hydra.langs.java.syntax.ClassTypeQualifier qualifier;
  
  public final hydra.langs.java.syntax.TypeIdentifier identifier;
  
  public final java.util.List<hydra.langs.java.syntax.TypeArgument> arguments;
  
  public ClassType (java.util.List<hydra.langs.java.syntax.Annotation> annotations, hydra.langs.java.syntax.ClassTypeQualifier qualifier, hydra.langs.java.syntax.TypeIdentifier identifier, java.util.List<hydra.langs.java.syntax.TypeArgument> arguments) {
    this.annotations = annotations;
    this.qualifier = qualifier;
    this.identifier = identifier;
    this.arguments = arguments;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ClassType)) {
      return false;
    }
    ClassType o = (ClassType) (other);
    return annotations.equals(o.annotations) && qualifier.equals(o.qualifier) && identifier.equals(o.identifier) && arguments.equals(o.arguments);
  }
  
  @Override
  public int hashCode() {
    return 2 * annotations.hashCode() + 3 * qualifier.hashCode() + 5 * identifier.hashCode() + 7 * arguments.hashCode();
  }
  
  public ClassType withAnnotations(java.util.List<hydra.langs.java.syntax.Annotation> annotations) {
    return new ClassType(annotations, qualifier, identifier, arguments);
  }
  
  public ClassType withQualifier(hydra.langs.java.syntax.ClassTypeQualifier qualifier) {
    return new ClassType(annotations, qualifier, identifier, arguments);
  }
  
  public ClassType withIdentifier(hydra.langs.java.syntax.TypeIdentifier identifier) {
    return new ClassType(annotations, qualifier, identifier, arguments);
  }
  
  public ClassType withArguments(java.util.List<hydra.langs.java.syntax.TypeArgument> arguments) {
    return new ClassType(annotations, qualifier, identifier, arguments);
  }
}