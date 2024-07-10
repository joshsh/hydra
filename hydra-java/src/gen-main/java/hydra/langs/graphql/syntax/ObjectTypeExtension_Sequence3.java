// Note: this is an automatically generated file. Do not edit.

package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ObjectTypeExtension_Sequence3 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ObjectTypeExtension.Sequence3");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces;
  
  public ObjectTypeExtension_Sequence3 (hydra.langs.graphql.syntax.Name name, hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    if (implementsInterfaces == null) {
      throw new IllegalArgumentException("null value for 'implementsInterfaces' argument");
    }
    this.name = name;
    this.implementsInterfaces = implementsInterfaces;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectTypeExtension_Sequence3)) {
      return false;
    }
    ObjectTypeExtension_Sequence3 o = (ObjectTypeExtension_Sequence3) (other);
    return name.equals(o.name) && implementsInterfaces.equals(o.implementsInterfaces);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * implementsInterfaces.hashCode();
  }
  
  public ObjectTypeExtension_Sequence3 withName(hydra.langs.graphql.syntax.Name name) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new ObjectTypeExtension_Sequence3(name, implementsInterfaces);
  }
  
  public ObjectTypeExtension_Sequence3 withImplementsInterfaces(hydra.langs.graphql.syntax.ImplementsInterfaces implementsInterfaces) {
    if (implementsInterfaces == null) {
      throw new IllegalArgumentException("null value for 'implementsInterfaces' argument");
    }
    return new ObjectTypeExtension_Sequence3(name, implementsInterfaces);
  }
}