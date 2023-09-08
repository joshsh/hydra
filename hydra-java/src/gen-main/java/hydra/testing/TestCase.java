package hydra.testing;

import java.io.Serializable;

/**
 * A simple test case with an input and an expected output
 */
public class TestCase<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/testing.TestCase");
  
  public final java.util.Optional<String> description;
  
  public final hydra.testing.EvaluationStyle evaluationStyle;
  
  public final hydra.core.Term<A> input;
  
  public final hydra.core.Term<A> output;
  
  public TestCase (java.util.Optional<String> description, hydra.testing.EvaluationStyle evaluationStyle, hydra.core.Term<A> input, hydra.core.Term<A> output) {
    this.description = description;
    this.evaluationStyle = evaluationStyle;
    this.input = input;
    this.output = output;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TestCase)) {
      return false;
    }
    TestCase o = (TestCase) (other);
    return description.equals(o.description) && evaluationStyle.equals(o.evaluationStyle) && input.equals(o.input) && output.equals(o.output);
  }
  
  @Override
  public int hashCode() {
    return 2 * description.hashCode() + 3 * evaluationStyle.hashCode() + 5 * input.hashCode() + 7 * output.hashCode();
  }
  
  public TestCase withDescription(java.util.Optional<String> description) {
    return new TestCase(description, evaluationStyle, input, output);
  }
  
  public TestCase withEvaluationStyle(hydra.testing.EvaluationStyle evaluationStyle) {
    return new TestCase(description, evaluationStyle, input, output);
  }
  
  public TestCase withInput(hydra.core.Term<A> input) {
    return new TestCase(description, evaluationStyle, input, output);
  }
  
  public TestCase withOutput(hydra.core.Term<A> output) {
    return new TestCase(description, evaluationStyle, input, output);
  }
}