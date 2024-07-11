// Note: this is an automatically generated file. Do not edit.

package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class ObjectTypeExtension_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ObjectTypeExtension.Sequence2");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final hydra.util.Opt<hydra.langs.graphql.syntax.ImplementsInterfaces> implementsInterfaces;
  
  public final hydra.util.Opt<hydra.langs.graphql.syntax.Directives> directives;
  
  public ObjectTypeExtension_Sequence2 (hydra.langs.graphql.syntax.Name name, hydra.util.Opt<hydra.langs.graphql.syntax.ImplementsInterfaces> implementsInterfaces, hydra.util.Opt<hydra.langs.graphql.syntax.Directives> directives) {
    java.util.Objects.requireNonNull((name));
    java.util.Objects.requireNonNull((implementsInterfaces));
    java.util.Objects.requireNonNull((directives));
    this.name = name;
    this.implementsInterfaces = implementsInterfaces;
    this.directives = directives;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectTypeExtension_Sequence2)) {
      return false;
    }
    ObjectTypeExtension_Sequence2 o = (ObjectTypeExtension_Sequence2) (other);
    return name.equals(o.name) && implementsInterfaces.equals(o.implementsInterfaces) && directives.equals(o.directives);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * implementsInterfaces.hashCode() + 5 * directives.hashCode();
  }
  
  public ObjectTypeExtension_Sequence2 withName(hydra.langs.graphql.syntax.Name name) {
    java.util.Objects.requireNonNull((name));
    return new ObjectTypeExtension_Sequence2(name, implementsInterfaces, directives);
  }
  
  public ObjectTypeExtension_Sequence2 withImplementsInterfaces(hydra.util.Opt<hydra.langs.graphql.syntax.ImplementsInterfaces> implementsInterfaces) {
    java.util.Objects.requireNonNull((implementsInterfaces));
    return new ObjectTypeExtension_Sequence2(name, implementsInterfaces, directives);
  }
  
  public ObjectTypeExtension_Sequence2 withDirectives(hydra.util.Opt<hydra.langs.graphql.syntax.Directives> directives) {
    java.util.Objects.requireNonNull((directives));
    return new ObjectTypeExtension_Sequence2(name, implementsInterfaces, directives);
  }
}