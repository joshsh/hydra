package hydra.langs.haskell.ast;

import java.io.Serializable;

public class PatternField implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.PatternField");
  
  public final hydra.langs.haskell.ast.Name name;
  
  public final hydra.langs.haskell.ast.Pattern pattern;
  
  public PatternField (hydra.langs.haskell.ast.Name name, hydra.langs.haskell.ast.Pattern pattern) {
    this.name = name;
    this.pattern = pattern;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PatternField)) {
      return false;
    }
    PatternField o = (PatternField) (other);
    return name.equals(o.name) && pattern.equals(o.pattern);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * pattern.hashCode();
  }
  
  public PatternField withName(hydra.langs.haskell.ast.Name name) {
    return new PatternField(name, pattern);
  }
  
  public PatternField withPattern(hydra.langs.haskell.ast.Pattern pattern) {
    return new PatternField(name, pattern);
  }
}