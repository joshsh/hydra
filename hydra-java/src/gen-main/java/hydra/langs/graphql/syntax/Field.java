package hydra.langs.graphql.syntax;

import java.io.Serializable;

public class Field implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.Field");
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Alias> alias;
  
  public final hydra.langs.graphql.syntax.Name name;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Arguments> arguments;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.Directives> directives;
  
  public final java.util.Optional<hydra.langs.graphql.syntax.SelectionSet> selectionSet;
  
  public Field (java.util.Optional<hydra.langs.graphql.syntax.Alias> alias, hydra.langs.graphql.syntax.Name name, java.util.Optional<hydra.langs.graphql.syntax.Arguments> arguments, java.util.Optional<hydra.langs.graphql.syntax.Directives> directives, java.util.Optional<hydra.langs.graphql.syntax.SelectionSet> selectionSet) {
    this.alias = alias;
    this.name = name;
    this.arguments = arguments;
    this.directives = directives;
    this.selectionSet = selectionSet;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Field)) {
      return false;
    }
    Field o = (Field) (other);
    return alias.equals(o.alias) && name.equals(o.name) && arguments.equals(o.arguments) && directives.equals(o.directives) && selectionSet.equals(o.selectionSet);
  }
  
  @Override
  public int hashCode() {
    return 2 * alias.hashCode() + 3 * name.hashCode() + 5 * arguments.hashCode() + 7 * directives.hashCode() + 11 * selectionSet.hashCode();
  }
  
  public Field withAlias(java.util.Optional<hydra.langs.graphql.syntax.Alias> alias) {
    return new Field(alias, name, arguments, directives, selectionSet);
  }
  
  public Field withName(hydra.langs.graphql.syntax.Name name) {
    return new Field(alias, name, arguments, directives, selectionSet);
  }
  
  public Field withArguments(java.util.Optional<hydra.langs.graphql.syntax.Arguments> arguments) {
    return new Field(alias, name, arguments, directives, selectionSet);
  }
  
  public Field withDirectives(java.util.Optional<hydra.langs.graphql.syntax.Directives> directives) {
    return new Field(alias, name, arguments, directives, selectionSet);
  }
  
  public Field withSelectionSet(java.util.Optional<hydra.langs.graphql.syntax.SelectionSet> selectionSet) {
    return new Field(alias, name, arguments, directives, selectionSet);
  }
}