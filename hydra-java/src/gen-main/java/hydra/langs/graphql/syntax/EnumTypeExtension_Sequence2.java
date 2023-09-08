package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class EnumTypeExtension_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.EnumTypeExtension.Sequence2");
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final hydra.langs.graphql.syntax.Directives directives;
  
  public EnumTypeExtension_Sequence2 (hydra.langs.graphql.syntax.Name name, hydra.langs.graphql.syntax.Directives directives) {
    this.name = name;
    this.directives = directives;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EnumTypeExtension_Sequence2)) {
      return false;
    }
    EnumTypeExtension_Sequence2 o = (EnumTypeExtension_Sequence2) (other);
    return name.equals(o.name) && directives.equals(o.directives);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * directives.hashCode();
  }
  
  public EnumTypeExtension_Sequence2 withName(hydra.langs.graphql.syntax.Name name) {
    return new EnumTypeExtension_Sequence2(name, directives);
  }
  
  public EnumTypeExtension_Sequence2 withDirectives(hydra.langs.graphql.syntax.Directives directives) {
    return new EnumTypeExtension_Sequence2(name, directives);
  }
}