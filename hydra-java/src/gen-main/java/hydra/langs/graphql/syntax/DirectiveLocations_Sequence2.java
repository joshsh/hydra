package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class DirectiveLocations_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.DirectiveLocations.Sequence2");
  
  public final java.util.Optional<java.lang.Void> or;
  
  public final hydra.langs.graphql.syntax.DirectiveLocation directiveLocation;
  
  public DirectiveLocations_Sequence2 (java.util.Optional<java.lang.Void> or, hydra.langs.graphql.syntax.DirectiveLocation directiveLocation) {
    this.or = or;
    this.directiveLocation = directiveLocation;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DirectiveLocations_Sequence2)) {
      return false;
    }
    DirectiveLocations_Sequence2 o = (DirectiveLocations_Sequence2) (other);
    return or.equals(o.or) && directiveLocation.equals(o.directiveLocation);
  }
  
  @Override
  public int hashCode() {
    return 2 * or.hashCode() + 3 * directiveLocation.hashCode();
  }
  
  public DirectiveLocations_Sequence2 withOr(java.util.Optional<java.lang.Void> or) {
    return new DirectiveLocations_Sequence2(or, directiveLocation);
  }
  
  public DirectiveLocations_Sequence2 withDirectiveLocation(hydra.langs.graphql.syntax.DirectiveLocation directiveLocation) {
    return new DirectiveLocations_Sequence2(or, directiveLocation);
  }
}