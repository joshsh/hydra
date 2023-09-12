package hydra.dsl;

import hydra.core.Elimination;
import hydra.core.Function;
import hydra.core.Term;
import hydra.dsl.prims.Strings;
import hydra.core.Name;
import org.junit.jupiter.api.Test;

import static hydra.dsl.Core.*;
import static hydra.dsl.Terms.*;
import static org.junit.jupiter.api.Assertions.*;


/**
 * Test illustrating the use of the Terms API in Java, which is used for constructing terms (untyped expressions).
 *
 * Note: for simplicity, these terms are annotated using the String class. A more typical annotation class is {@link hydra.compute.Kv}
 */
@SuppressWarnings("unchecked")
public class TermsTest {
  /**
   * See {@link hydra.dsl.TypesTest} for the record type corresponding to this term
   */
  private final Term<String> bayAreaLatLon = record("LatLon", // records always have a name
      field("lat", float32(37.7749f)), field("lon", float32(-122.4194f)));

  /**
   * An injection term chooses one of the variants of a union type, and supplies an appropriate term
   *
   * See {@link hydra.dsl.TypesTest} for the union type corresponding to this term
   */
  private final Term<String> bayAreaLocation = inject("Location", field("latlon", bayAreaLatLon));

  /**
   * See {@link hydra.dsl.TypesTest} for a function type corresponding to this term
   */
  private final Term<String> stringLength = primitive("hydra/lib/strings.length");

  private final Term<String> cat3 =
      lambda("s1", lambda("s2", lambda("s3", apply(Strings.cat(), list(variable("s1"), variable("s2"), variable("s3"))))));

  private final Term<String> longitude = projection("LatLon", "lon");

  private final Term<String> longitudeAnnotated = annot("Gets the longitude from a LatLon", longitude);

  private <A> Term.PartialVisitor<A, Integer> countBoundVariables() {
      return new Term.PartialVisitor<A, Integer>() {
          @Override
          public Integer visit(Term.Annotated<A> instance) {
              return instance.value.subject.accept(countBoundVariables());
          }

          @Override
          public Integer visit(Term.Function<A> instance) {
              return instance.value.accept(new Function.PartialVisitor<A, Integer>() {
                  @Override
                  public Integer otherwise(Function<A> instance) {
                      return 0;
                  }

                  @Override
                  public Integer visit(Function.Lambda<A> instance) {
                      return 1 + instance.value.body.accept(countBoundVariables());
                  }
              });
          }

          @Override
          public Integer otherwise(Term<A> ignored) {
              return 0;
          }
      };
  }

  @Test
  public void constructedTermsAreAsExpected() {
    assertTrue(bayAreaLatLon instanceof Term.Record);
    assertEquals(name("LatLon"), ((Term.Record<String>) bayAreaLatLon).value.typeName);
    assertEquals(float32(-122.4194f), ((Term.Record<String>) bayAreaLatLon).value.fields.get(1).term);

    assertTrue(bayAreaLocation instanceof Term.Union);
    assertEquals(name("Location"), ((Term.Union<String>) bayAreaLocation).value.typeName);
    assertEquals(fieldName("latlon"), ((Term.Union<String>) bayAreaLocation).value.field.name);

    assertTrue(Strings.length() instanceof Term.Function);
    assertTrue(((Term.Function<Object>) Strings.length()).value instanceof Function.Primitive);
    assertEquals(name("hydra/lib/strings.length"),
        ((Function.Primitive<Object>) ((Term.Function<Object>) Strings.length()).value).value);

    assertTrue(cat3 instanceof Term.Function);
    assertTrue(((Term.Function<String>) cat3).value instanceof Function.Lambda);
    assertEquals(new Name("s1"), ((Function.Lambda<String>) ((Term.Function<String>) cat3).value).value.parameter);

    assertTrue(longitude instanceof Term.Function);
    assertTrue(((Term.Function<String>) longitude).value instanceof Function.Elimination);
    assertTrue(
        ((Function.Elimination<String>) ((Term.Function<String>) longitude).value).value instanceof Elimination.Record);
    assertEquals(name("LatLon"),
        ((Elimination.Record<String>) ((Function.Elimination<String>) ((Term.Function<String>) longitude).value).value).value.typeName);
    assertEquals(fieldName("lon"),
        ((Elimination.Record<String>) ((Function.Elimination<String>) ((Term.Function<String>) longitude).value).value).value.field);

    assertTrue(longitudeAnnotated instanceof Term.Annotated);
    // Notice that annotations, here, are String-valued
    assertEquals("Gets the longitude from a LatLon", ((Term.Annotated<String>) longitudeAnnotated).value.annotation);
    assertEquals(longitude, ((Term.Annotated<String>) longitudeAnnotated).value.subject);
  }

  @Test
  public void demonstrateVisitor() {
    assertEquals(0, bayAreaLatLon.accept(countBoundVariables()));
    assertEquals(3, cat3.accept(countBoundVariables()));
  }
}
