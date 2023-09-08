package hydra.langs.java.syntax;

import java.io.Serializable;

public class MethodReference_New implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.MethodReference.New");
  
  public final hydra.langs.java.syntax.ClassType classType;
  
  public final java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments;
  
  public MethodReference_New (hydra.langs.java.syntax.ClassType classType, java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments) {
    this.classType = classType;
    this.typeArguments = typeArguments;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof MethodReference_New)) {
      return false;
    }
    MethodReference_New o = (MethodReference_New) (other);
    return classType.equals(o.classType) && typeArguments.equals(o.typeArguments);
  }
  
  @Override
  public int hashCode() {
    return 2 * classType.hashCode() + 3 * typeArguments.hashCode();
  }
  
  public MethodReference_New withClassType(hydra.langs.java.syntax.ClassType classType) {
    return new MethodReference_New(classType, typeArguments);
  }
  
  public MethodReference_New withTypeArguments(java.util.List<hydra.langs.java.syntax.TypeArgument> typeArguments) {
    return new MethodReference_New(classType, typeArguments);
  }
}