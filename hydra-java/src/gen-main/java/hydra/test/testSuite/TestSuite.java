package hydra.test.testSuite;

/**
 * Test cases for primitive functions
 */
public interface TestSuite {
  static hydra.testing.TestGroup<hydra.compute.Kv> allTests() {
    return new hydra.testing.TestGroup("All tests", java.util.Optional.empty(), java.util.Arrays.asList(
      new hydra.testing.TestGroup("hydra/lib/lists primitives", java.util.Optional.empty(), java.util.Arrays.asList(
        new hydra.testing.TestGroup("apply", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.apply"))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.toUpper"))),
          new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.toLower"))))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("One")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("Two")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("Three")))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("ONE")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("TWO")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("THREE")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("three"))))))),
        new hydra.testing.TestGroup("bind", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.bind"))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(4))))))), new hydra.core.Term.Function(new hydra.core.Function.Lambda(new hydra.core.Lambda(new hydra.core.Name("x"), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.pure"))), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/math.neg"))), new hydra.core.Term.Variable(new hydra.core.Name("x"))))))))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(-1))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(-2))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(-3))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(-4)))))))),
        new hydra.testing.TestGroup("concat", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.concat"))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))))),
          new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(4))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(5))))),
          new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(6))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(7))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(8))))))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(4))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(5))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(6))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(7))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(8)))))))),
        new hydra.testing.TestGroup("head", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.head"))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))))))), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1)))))),
        new hydra.testing.TestGroup("intercalate", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.intercalate"))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(0))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(0))))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))))),
          new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(4))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(5))))),
          new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(6))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(7))),
            new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(8))))))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(0))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(0))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(4))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(5))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(0))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(0))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(6))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(7))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(8)))))))),
        new hydra.testing.TestGroup("intersperse", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.intersperse"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("and")))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("three")))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("and")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("and")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("three"))))))),
        new hydra.testing.TestGroup("last", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.last"))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))))))), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3)))))),
        new hydra.testing.TestGroup("length", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.length"))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(2))),
          new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3))))))), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3)))))),
        new hydra.testing.TestGroup("map", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.map"))), new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.toUpper"))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")))))), new hydra.core.Term.List(java.util.Arrays.asList(
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("ONE")),
          new hydra.core.Term.Literal(new hydra.core.Literal.String_("TWO"))))))),
        new hydra.testing.TestGroup("pure", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/lists.pure"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")))), new hydra.core.Term.List(java.util.Arrays.asList(new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")))))))), java.util.Arrays.asList()),
      new hydra.testing.TestGroup("hydra/lib/strings primitives", java.util.Optional.empty(), java.util.Arrays.asList(
        new hydra.testing.TestGroup("cat", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.cat"))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("three")))))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("onetwothree"))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.cat"))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")))))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("one"))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.cat"))), new hydra.core.Term.List(java.util.Arrays.asList()))), new hydra.core.Term.Literal(new hydra.core.Literal.String_(""))))),
        new hydra.testing.TestGroup("length", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.length"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("")))), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(0)))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.length"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("a")))), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(1)))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.length"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")))), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(3)))))),
        new hydra.testing.TestGroup("splitOn", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("ss")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("Mississippi")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("Mi")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("i")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("ippi"))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("Mississippi")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("Mississippi")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_(""))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_(" ")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("one two three")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("three"))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_(" ")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_(" one two three ")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("three")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_(""))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_(" ")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("  one two three")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("one")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("two")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("three"))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("  ")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("  one two three")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("one two three"))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("aa")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("aaa")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("a"))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("a")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("")))), new hydra.core.Term.List(java.util.Arrays.asList(new hydra.core.Term.Literal(new hydra.core.Literal.String_(""))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("abc")))), new hydra.core.Term.List(java.util.Arrays.asList(
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("a")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("b")),
            new hydra.core.Term.Literal(new hydra.core.Literal.String_("c"))))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.splitOn"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("")))), new hydra.core.Term.List(java.util.Arrays.asList(new hydra.core.Term.Literal(new hydra.core.Literal.String_(""))))))),
        new hydra.testing.TestGroup("toLower", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.toLower"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("One TWO threE")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("one two three"))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.toLower"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("Abc123")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("abc123"))))),
        new hydra.testing.TestGroup("toUpper", java.util.Optional.empty(), java.util.Arrays.asList(), java.util.Arrays.asList(
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.toUpper"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("One TWO threE")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("ONE TWO THREE"))),
          new hydra.testing.TestCase(java.util.Optional.empty(), new hydra.testing.EvaluationStyle.Eager(), new hydra.core.Term.Application(new hydra.core.Application(new hydra.core.Term.Function(new hydra.core.Function.Primitive(new hydra.core.Name("hydra/lib/strings.toUpper"))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("Abc123")))), new hydra.core.Term.Literal(new hydra.core.Literal.String_("ABC123")))))), java.util.Arrays.asList())), java.util.Arrays.asList());
  }
}