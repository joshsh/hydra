// Note: this is an automatically generated file. Do not edit.

package hydra.testing;

import java.io.Serializable;

/**
 * A collection of test cases with a name and optional description
 */
public class TestGroup<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/testing.TestGroup");
  
  public final String name;
  
  public final java.util.Optional<String> description;
  
  public final java.util.List<hydra.testing.TestGroup<A>> subgroups;
  
  public final java.util.List<hydra.testing.TestCase<A>> cases;
  
  public TestGroup (String name, java.util.Optional<String> description, java.util.List<hydra.testing.TestGroup<A>> subgroups, java.util.List<hydra.testing.TestCase<A>> cases) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    if (description == null) {
      throw new IllegalArgumentException("null value for 'description' argument");
    }
    if (subgroups == null) {
      throw new IllegalArgumentException("null value for 'subgroups' argument");
    }
    if (cases == null) {
      throw new IllegalArgumentException("null value for 'cases' argument");
    }
    this.name = name;
    this.description = description;
    this.subgroups = subgroups;
    this.cases = cases;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TestGroup)) {
      return false;
    }
    TestGroup o = (TestGroup) (other);
    return name.equals(o.name) && description.equals(o.description) && subgroups.equals(o.subgroups) && cases.equals(o.cases);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * description.hashCode() + 5 * subgroups.hashCode() + 7 * cases.hashCode();
  }
  
  public TestGroup withName(String name) {
    if (name == null) {
      throw new IllegalArgumentException("null value for 'name' argument");
    }
    return new TestGroup(name, description, subgroups, cases);
  }
  
  public TestGroup withDescription(java.util.Optional<String> description) {
    if (description == null) {
      throw new IllegalArgumentException("null value for 'description' argument");
    }
    return new TestGroup(name, description, subgroups, cases);
  }
  
  public TestGroup withSubgroups(java.util.List<hydra.testing.TestGroup<A>> subgroups) {
    if (subgroups == null) {
      throw new IllegalArgumentException("null value for 'subgroups' argument");
    }
    return new TestGroup(name, description, subgroups, cases);
  }
  
  public TestGroup withCases(java.util.List<hydra.testing.TestCase<A>> cases) {
    if (cases == null) {
      throw new IllegalArgumentException("null value for 'cases' argument");
    }
    return new TestGroup(name, description, subgroups, cases);
  }
}