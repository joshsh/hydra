package hydra;

import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.core.Field;
import hydra.core.Name;
import hydra.core.Record;
import hydra.core.Term;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import org.junit.jupiter.api.Test;

import static hydra.Rewriting.*;
import static hydra.dsl.Terms.*;
import static hydra.Flows.*;
import static org.junit.jupiter.api.Assertions.*;


public class RewritingTest {
    private static final Name bboxName = new Name("BoundingBox");
    private static final Name geoPointName = new Name("GeoPoint");
    private static final Name stateGeoName = new Name("StateGeometry");

    private static final Term<String> caBbox = annot("Bounding box for California", record(bboxName, field("southwest",
        record(geoPointName, field("lat", float32(32.534156f)), field("lon", float32(-124.409591f)))),
        field("northeast",
            record(geoPointName, field("lat", float32(42.009518f)), field("lon", float32(-114.131211f))))));

    private static final Term<String> caCapital = annot("Coordinates of Sacramento",
        record(geoPointName, field("lat", float32(38.5816f)), field("lon", annot("fail here", float32(-121.4944f)))));

    private static final Term<String> caGeom = annot("Geometry of California",
        record(stateGeoName, field("boundingBox", caBbox), field("capital", caCapital)));

    private static final Term<String> listOfStates = annot("A list of states", list(caGeom, caGeom, caGeom));

    @Test
    public void checkFailure() {
        FlowState<Integer, Term<String>> resultState = applyFailOnSpecialAnnotation(listOfStates, 0);
        assertFalse(resultState.value.isPresent());
        assertEquals(1, resultState.trace.messages.size());
        assertTrue(resultState.trace.messages.get(0).startsWith("Error: "));
    }

    @Test
    public void checkSimpleRewritingScenarios() {
        FlowState<Integer, Term<String>> resultState = applyCapitalizeFieldNames(listOfStates);

        // Check modified fields
        Optional<Term<String>> result = resultState.value;
        assertTrue(result.isPresent());
        assertTrue(result.get() instanceof Term.Annotated);
        Term<String> list = ((Term.Annotated<String>) result.get()).value.subject;
        assertTrue(list instanceof Term.List);
        List<Term<String>> vals = ((Term.List<String>) list).value;
        assertEquals(3, vals.size());
        Term<String> stateAnn = vals.get(2);
        assertTrue(stateAnn instanceof Term.Annotated);
        Term<String> state = ((Term.Annotated<String>) stateAnn).value.subject;
        assertTrue(state instanceof Term.Record);
        List<Field<String>> fields = ((Term.Record<String>) state).value.fields;
        assertEquals(2, fields.size());
        Field<String> bboxfield = fields.get(0);
        assertEquals("BOUNDINGBOX", bboxfield.name.value);
        Field<String> capitalField = fields.get(1);
        assertEquals("CAPITAL", capitalField.name.value);

        // Check modified state
        int pointFields = 2;
        int bboxFields = 2 + 2*pointFields;
        int stateFields = 2 + pointFields + bboxFields;
        int listlen = 3;
        int totalFields = listlen * stateFields;
        assertEquals(Integer.valueOf(totalFields), resultState.state);
    }

    // Capitalizes record field names, and also counts the number of fields mutated
    private static <A> Flow<Integer, Term<A>> capitalizeFieldNames(
        Function<Term<A>, Flow<Integer, Term<A>>> recurse,
        Term<A> original) {
        return original.accept(new Term.PartialVisitor<A, Flow<Integer, Term<A>>>() {
            @Override
            public Flow<Integer, Term<A>> otherwise(Term instance) {
                Term<A> inst = instance;
                return recurse.apply(inst);
            }

            @Override
            public Flow<Integer, Term<A>> visit(Term.Record instance) {
                Record<A> rec = instance.value;
                Flow<Integer, List<Field<A>>> modFields = mapM(rec.fields, field -> bind(getState(),
                    count -> bind(putState(count + 1), ignore -> map(capitalizeFieldNames(recurse, field.term),
                        term -> field(field.name.value.toUpperCase(), term)))));
                return map(modFields, fields -> new Term.Record<>(new Record<>(instance.value.typeName, fields)));
            }
        });
    }

    private static FlowState<Integer, Term<String>> applyCapitalizeFieldNames(Term<String> source) {
        Flow<Integer, Term<String>> flow1 = rewriteTermM(recurse -> t -> capitalizeFieldNames(recurse, t), Flows::pure, source);
        return flow1.value.apply(0).apply(EMPTY_TRACE);
    }

    private static <S> Flow<S, Term<String>> failOnSpecialAnnotation(
        Function<Term<String>, Flow<S, Term<String>>> recurse,
        Term<String> original) {
        return original.accept(new Term.PartialVisitor<String, Flow<S, Term<String>>>() {
            @Override
            public Flow<S, Term<String>> otherwise(Term instance) {
                return recurse.apply(instance);
            }

            @Override
            public Flow<S, Term<String>> visit(Term.Annotated instance) {
                Term.Annotated<String> t = instance;
                return t.value.annotation.equals("fail here") ? Flows.fail("Bad annotation!") : recurse.apply(instance);
            }
        });
    }

    private static <S> FlowState<S, Term<String>> applyFailOnSpecialAnnotation(Term<String> source, S seed) {
        Flow<S, Term<String>> flow1 = rewriteTermM(recurse -> t -> failOnSpecialAnnotation(recurse, t), Flows::pure, source);
        return flow1.value.apply(seed).apply(EMPTY_TRACE);
    }
}
