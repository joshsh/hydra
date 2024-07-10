// Note: this is an automatically generated file. Do not edit.

package hydra.grammar;

import java.io.Serializable;

/**
 * A pattern together with a name (label)
 */
public class LabeledPattern implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/grammar.LabeledPattern");
  
  public final hydra.grammar.Label label;
  
  public final hydra.grammar.Pattern pattern;
  
  public LabeledPattern (hydra.grammar.Label label, hydra.grammar.Pattern pattern) {
    if (label == null) {
      throw new IllegalArgumentException("null value for 'label' argument");
    }
    if (pattern == null) {
      throw new IllegalArgumentException("null value for 'pattern' argument");
    }
    this.label = label;
    this.pattern = pattern;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof LabeledPattern)) {
      return false;
    }
    LabeledPattern o = (LabeledPattern) (other);
    return label.equals(o.label) && pattern.equals(o.pattern);
  }
  
  @Override
  public int hashCode() {
    return 2 * label.hashCode() + 3 * pattern.hashCode();
  }
  
  public LabeledPattern withLabel(hydra.grammar.Label label) {
    if (label == null) {
      throw new IllegalArgumentException("null value for 'label' argument");
    }
    return new LabeledPattern(label, pattern);
  }
  
  public LabeledPattern withPattern(hydra.grammar.Pattern pattern) {
    if (pattern == null) {
      throw new IllegalArgumentException("null value for 'pattern' argument");
    }
    return new LabeledPattern(label, pattern);
  }
}