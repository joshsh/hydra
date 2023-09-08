package hydra.langs.java.syntax;

import java.io.Serializable;

public class TypeBound_ClassOrInterface implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.TypeBound.ClassOrInterface");
  
  public final hydra.langs.java.syntax.ClassOrInterfaceType type;
  
  public final java.util.List<hydra.langs.java.syntax.AdditionalBound> additional;
  
  public TypeBound_ClassOrInterface (hydra.langs.java.syntax.ClassOrInterfaceType type, java.util.List<hydra.langs.java.syntax.AdditionalBound> additional) {
    this.type = type;
    this.additional = additional;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeBound_ClassOrInterface)) {
      return false;
    }
    TypeBound_ClassOrInterface o = (TypeBound_ClassOrInterface) (other);
    return type.equals(o.type) && additional.equals(o.additional);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * additional.hashCode();
  }
  
  public TypeBound_ClassOrInterface withType(hydra.langs.java.syntax.ClassOrInterfaceType type) {
    return new TypeBound_ClassOrInterface(type, additional);
  }
  
  public TypeBound_ClassOrInterface withAdditional(java.util.List<hydra.langs.java.syntax.AdditionalBound> additional) {
    return new TypeBound_ClassOrInterface(type, additional);
  }
}