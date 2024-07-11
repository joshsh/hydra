// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

public class ValueBinding_Simple implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.ValueBinding.Simple");
  
  public final hydra.langs.haskell.ast.Pattern pattern;
  
  public final hydra.langs.haskell.ast.RightHandSide rhs;
  
  public final hydra.util.Opt<hydra.langs.haskell.ast.LocalBindings> localBindings;
  
  public ValueBinding_Simple (hydra.langs.haskell.ast.Pattern pattern, hydra.langs.haskell.ast.RightHandSide rhs, hydra.util.Opt<hydra.langs.haskell.ast.LocalBindings> localBindings) {
    java.util.Objects.requireNonNull((pattern));
    java.util.Objects.requireNonNull((rhs));
    java.util.Objects.requireNonNull((localBindings));
    this.pattern = pattern;
    this.rhs = rhs;
    this.localBindings = localBindings;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ValueBinding_Simple)) {
      return false;
    }
    ValueBinding_Simple o = (ValueBinding_Simple) (other);
    return pattern.equals(o.pattern) && rhs.equals(o.rhs) && localBindings.equals(o.localBindings);
  }
  
  @Override
  public int hashCode() {
    return 2 * pattern.hashCode() + 3 * rhs.hashCode() + 5 * localBindings.hashCode();
  }
  
  public ValueBinding_Simple withPattern(hydra.langs.haskell.ast.Pattern pattern) {
    java.util.Objects.requireNonNull((pattern));
    return new ValueBinding_Simple(pattern, rhs, localBindings);
  }
  
  public ValueBinding_Simple withRhs(hydra.langs.haskell.ast.RightHandSide rhs) {
    java.util.Objects.requireNonNull((rhs));
    return new ValueBinding_Simple(pattern, rhs, localBindings);
  }
  
  public ValueBinding_Simple withLocalBindings(hydra.util.Opt<hydra.langs.haskell.ast.LocalBindings> localBindings) {
    java.util.Objects.requireNonNull((localBindings));
    return new ValueBinding_Simple(pattern, rhs, localBindings);
  }
}