package hydra.dsl;

import hydra.core.Name;
import hydra.core.Term;
import hydra.core.Type;
import hydra.core.WrappedType;
import org.junit.jupiter.api.Test;

import static hydra.dsl.Core.fieldName;
import static hydra.dsl.Core.name;
import static hydra.dsl.Types.annot;
import static hydra.dsl.Types.field;
import static hydra.dsl.Types.float32;
import static hydra.dsl.Types.float64;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.int32;
import static hydra.dsl.Types.record;
import static hydra.dsl.Types.string;
import static hydra.dsl.Types.union;
import static hydra.dsl.Types.wrap;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;


/**
 * Test illustrating the use of the Types API in Java, which is used for constructing type definitions.
 */
@SuppressWarnings("unchecked")
public class TypesTest {

    private final Type latLonType = record("LatLon", // record types always have a name
            field("lat", float32()),
            field("lon", float32()));

    private final Type locationType = union("Location",
            field("name", string()),
            field("latlon", wrap("LatLon", float32()))); // refer to named types using nominal(name)

    private final Type stringToIntType = function(
            string(), int32());

    private final Type pairOfLatLonsToFloatType = function(
            wrap("LatLon", float32()), wrap("LatLon", float32()), float32());

    private final Type annotatedType = annot(
            new Name("description"), Terms.string("this is a string-annotated double type"), float64());

    @Test
    public void constructedTypesAreAsExpected() {
        assertTrue(latLonType instanceof Type.Record);
        assertEquals(name("LatLon"), ((Type.Record) latLonType).value.typeName);
        assertEquals(fieldName("lat"), ((Type.Record) latLonType).value.fields.get(0).name);

        assertTrue(locationType instanceof Type.Union);
        assertEquals(name("Location"), ((Type.Union) locationType).value.typeName);
        assertEquals(fieldName("latlon"), ((Type.Union) locationType).value.fields.get(1).name);

        assertTrue(stringToIntType instanceof Type.Function);
        assertEquals(string(), ((Type.Function) stringToIntType).value.domain);
        assertEquals(int32(), ((Type.Function) stringToIntType).value.codomain);

        assertTrue(pairOfLatLonsToFloatType instanceof Type.Function);
        assertTrue(((Type.Function) pairOfLatLonsToFloatType).value.domain instanceof Type.Wrap);
        assertEquals(new WrappedType(name("LatLon"), float32()),
                ((Type.Wrap) ((Type.Function) pairOfLatLonsToFloatType).value.domain).value);

        assertTrue(annotatedType instanceof Type.Annotated);
        // Notice that annotations, here, are String-valued
        assertHasDescription(annotatedType, "this is a string-annotated double type");
        assertEquals(float64(), ((Type.Annotated) annotatedType).value.subject);
    }

    @Test
    public void demonstrateVisitor() {
        Type.PartialVisitor<Integer> countFields = new Type.PartialVisitor<Integer>() {
            @Override
            public Integer visit(Type.Record instance) {
                return instance.value.fields.size();
            }

            @Override
            public Integer visit(Type.Union instance) {
                return instance.value.fields.size();
            }

            @Override
            public Integer otherwise(Type ignored) {
                return 0;
            }
        };

        assertEquals(2, latLonType.accept(countFields));
        assertEquals(2, locationType.accept(countFields));
        assertEquals(0, stringToIntType.accept(countFields));
    }

    private void assertHasDescription(Type type, String expected) {
        String desc = type.accept(new Type.PartialVisitor<>() {
            @Override
            public String visit(Type.Annotated instance) {
                Term desc = instance.value.annotation.get(new Name("description"));
                return Flows.fromFlow(Expect.string(desc));
            }

            @Override
            public String otherwise(Type ignored) {
                fail("not annotated");
                return null;
            }
        });

        assertEquals(expected, desc);
    }
}
