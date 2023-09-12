package hydra.printing;

/**
 * Utilities for use in transformations
 */
public interface Printing {
  static String describeFloatType(hydra.core.FloatType t) {
    return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
      hydra.printing.Printing.describePrecision(hydra.basics.Basics.floatTypePrecision((t))),
      " floating-point numbers"));
  }
  
  static String describeIntegerType(hydra.core.IntegerType t) {
    return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
      hydra.printing.Printing.describePrecision(hydra.basics.Basics.integerTypePrecision((t))),
      " integers"));
  }
  
  static String describeLiteralType(hydra.core.LiteralType v1) {
    return ((v1)).accept(new hydra.core.LiteralType.Visitor<String>() {
      @Override
      public String visit(hydra.core.LiteralType.Binary instance) {
        return "binary strings";
      }
      
      @Override
      public String visit(hydra.core.LiteralType.Boolean_ instance) {
        return "boolean values";
      }
      
      @Override
      public String visit(hydra.core.LiteralType.Float_ instance) {
        return hydra.printing.Printing.describeFloatType((instance.value));
      }
      
      @Override
      public String visit(hydra.core.LiteralType.Integer_ instance) {
        return hydra.printing.Printing.describeIntegerType((instance.value));
      }
      
      @Override
      public String visit(hydra.core.LiteralType.String_ instance) {
        return "character strings";
      }
    });
  }
  
  static String describePrecision(hydra.mantle.Precision v1) {
    return ((v1)).accept(new hydra.mantle.Precision.Visitor<String>() {
      @Override
      public String visit(hydra.mantle.Precision.Arbitrary instance) {
        return "arbitrary-precision";
      }
      
      @Override
      public String visit(hydra.mantle.Precision.Bits instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          hydra.lib.literals.ShowInt32.apply((instance.value)),
          "-bit"));
      }
    });
  }
  
  static <A> String describeType(hydra.core.Type<A> v1) {
    return ((v1)).accept(new hydra.core.Type.Visitor<A, String>() {
      @Override
      public String visit(hydra.core.Type.Annotated<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "annotated ",
          hydra.printing.Printing.describeType(((instance.value)).subject)));
      }
      
      @Override
      public String visit(hydra.core.Type.Application<A> instance) {
        return "instances of an application type";
      }
      
      @Override
      public String visit(hydra.core.Type.Literal<A> instance) {
        return hydra.printing.Printing.describeLiteralType((instance.value));
      }
      
      @Override
      public String visit(hydra.core.Type.Function<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
            hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
              "functions from ",
              hydra.printing.Printing.describeType(((instance.value)).domain))),
            " to ")),
          hydra.printing.Printing.describeType(((instance.value)).codomain)));
      }
      
      @Override
      public String visit(hydra.core.Type.Lambda<A> instance) {
        return "polymorphic terms";
      }
      
      @Override
      public String visit(hydra.core.Type.List<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "lists of ",
          hydra.printing.Printing.describeType((instance.value))));
      }
      
      @Override
      public String visit(hydra.core.Type.Map<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
            hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
              "maps from ",
              hydra.printing.Printing.describeType(((instance.value)).keys))),
            " to ")),
          hydra.printing.Printing.describeType(((instance.value)).values)));
      }
      
      @Override
      public String visit(hydra.core.Type.Optional<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "optional ",
          hydra.printing.Printing.describeType((instance.value))));
      }
      
      @Override
      public String visit(hydra.core.Type.Product<A> instance) {
        return "tuples";
      }
      
      @Override
      public String visit(hydra.core.Type.Record<A> instance) {
        return "records";
      }
      
      @Override
      public String visit(hydra.core.Type.Set<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "sets of ",
          hydra.printing.Printing.describeType((instance.value))));
      }
      
      @Override
      public String visit(hydra.core.Type.Stream<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "streams of ",
          hydra.printing.Printing.describeType((instance.value))));
      }
      
      @Override
      public String visit(hydra.core.Type.Sum<A> instance) {
        return "variant tuples";
      }
      
      @Override
      public String visit(hydra.core.Type.Union<A> instance) {
        return "unions";
      }
      
      @Override
      public String visit(hydra.core.Type.Variable<A> instance) {
        return "instances of a named type";
      }
      
      @Override
      public String visit(hydra.core.Type.Wrap<A> instance) {
        return hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "wrapper for ",
          hydra.printing.Printing.describeType(((instance.value)).object)));
      }
    });
  }
}