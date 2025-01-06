package hydra.dsl;

import hydra.core.Elimination;
import hydra.core.Function;
import hydra.core.Term;
import hydra.dsl.prims.Strings;
import hydra.core.Name;
import org.junit.jupiter.api.Test;

import static hydra.dsl.Core.fieldName;
import static hydra.dsl.Core.name;
import static hydra.dsl.Terms.annot;
import static hydra.dsl.Terms.apply;
import static hydra.dsl.Terms.field;
import static hydra.dsl.Terms.float32;
import static hydra.dsl.Terms.inject;
import static hydra.dsl.Terms.lambda;
import static hydra.dsl.Terms.list;
import static hydra.dsl.Terms.primitive;
import static hydra.dsl.Terms.project;
import static hydra.dsl.Terms.record;
import static hydra.dsl.Terms.variable;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;


/**
 * Test illustrating the use of the Terms API in Java, which is used for constructing terms (untyped expressions).
 */
@SuppressWarnings("unchecked")
public class TermsTest {
    /**
     * See {@link hydra.dsl.TypesTest} for the record type corresponding to this term.
     */
    private final Term bayAreaLatLon = record("LatLon", // records always have a name
            field("lat", float32(37.7749f)), field("lon", float32(-122.4194f)));

    /**
     * An injection term chooses one of the variants of a union type, and supplies an appropriate term.
     * See {@link hydra.dsl.TypesTest} for the union type corresponding to this term
     */
    private final Term bayAreaLocation = inject("Location", field("latlon", bayAreaLatLon));

    /**
     * See {@link hydra.dsl.TypesTest} for a function type corresponding to this term.
     */
    private final Term stringLength = primitive("hydra/lib/strings.length");

    private final Term cat3 =
            lambda("s1", lambda("s2",
                    lambda("s3", apply(Strings.cat(), list(variable("s1"), variable("s2"), variable("s3"))))));

    private final Term longitude = project("LatLon", "lon");

    private final Term longitudeAnnotated = annot(
            new Name("description"), Terms.string("Gets the longitude from a LatLon"),
            longitude);

    private Term.PartialVisitor<Integer> countBoundVariables() {
        return new Term.PartialVisitor<Integer>() {
            @Override
            public Integer visit(Term.Annotated instance) {
                return instance.value.subject.accept(countBoundVariables());
            }

            @Override
            public Integer visit(Term.Function instance) {
                return instance.value.accept(new Function.PartialVisitor<Integer>() {
                    @Override
                    public Integer otherwise(Function instance) {
                        return 0;
                    }

                    @Override
                    public Integer visit(Function.Lambda instance) {
                        return 1 + instance.value.body.accept(countBoundVariables());
                    }
                });
            }

            @Override
            public Integer otherwise(Term ignored) {
                return 0;
            }
        };
    }

    @Test
    public void constructedTermsAreAsExpected() {
        assertTrue(bayAreaLatLon instanceof Term.Record);
        assertEquals(name("LatLon"), ((Term.Record) bayAreaLatLon).value.typeName);
        assertEquals(float32(-122.4194f), ((Term.Record) bayAreaLatLon).value.fields.get(1).term);

        assertTrue(bayAreaLocation instanceof Term.Union);
        assertEquals(name("Location"), ((Term.Union) bayAreaLocation).value.typeName);
        assertEquals(fieldName("latlon"), ((Term.Union) bayAreaLocation).value.field.name);

        assertTrue(Strings.length() instanceof Term.Function);
        assertTrue(((Term.Function) Strings.length()).value instanceof Function.Primitive);
        assertEquals(name("hydra/lib/strings.length"),
                ((Function.Primitive) ((Term.Function) Strings.length()).value).value);

        assertTrue(cat3 instanceof Term.Function);
        assertTrue(((Term.Function) cat3).value instanceof Function.Lambda);
        assertEquals(new Name("s1"),
                ((Function.Lambda) ((Term.Function) cat3).value).value.parameter);

        assertTrue(longitude instanceof Term.Function);
        assertTrue(((Term.Function) longitude).value instanceof Function.Elimination);
        assertTrue(
                ((Function.Elimination) ((Term.Function) longitude).value).value instanceof Elimination.Record);
        assertEquals(name("LatLon"),
                ((Elimination.Record) ((Function.Elimination) ((Term.Function) longitude).value).value)
                        .value.typeName);
        assertEquals(fieldName("lon"),
                ((Elimination.Record) ((Function.Elimination) ((Term.Function) longitude).value).value)
                        .value.field);

        assertTrue(longitudeAnnotated instanceof Term.Annotated);
        // Notice that annotations, here, are String-valued
        assertHasDescription(longitudeAnnotated, "Gets the longitude from a LatLon");
        assertEquals(longitude, ((Term.Annotated) longitudeAnnotated).value.subject);
    }

    @Test
    public void demonstrateVisitor() {
        assertEquals(0, bayAreaLatLon.accept(countBoundVariables()));
        assertEquals(3, cat3.accept(countBoundVariables()));
    }

    private void assertHasDescription(Term term, String expected) {
        String desc = term.accept(new Term.PartialVisitor<>() {
            @Override
            public String visit(Term.Annotated instance) {
                Term desc = instance.value.annotation.get(new Name("description"));
                return Flows.fromFlow(Expect.string(desc));
            }

            @Override
            public String otherwise(Term ignored) {
                fail("not annotated");
                return null;
            }
        });

        assertEquals(expected, desc);
    }
}
