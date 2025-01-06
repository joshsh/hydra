package hydra;

import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.core.Field;
import hydra.core.Name;
import hydra.core.Record;
import hydra.core.Term;

import hydra.dsl.Flows;
import java.util.List;

import hydra.dsl.Terms;
import hydra.util.Opt;

import java.util.Map;
import java.util.function.Function;

import org.junit.jupiter.api.Test;

import static hydra.dsl.Flows.EMPTY_TRACE;
import static hydra.dsl.Flows.bind;
import static hydra.dsl.Flows.getState;
import static hydra.dsl.Flows.map;
import static hydra.dsl.Flows.mapM;
import static hydra.dsl.Flows.putState;
import static hydra.Rewriting.rewriteTermM;
import static hydra.dsl.Terms.annot;
import static hydra.dsl.Terms.field;
import static hydra.dsl.Terms.float32;
import static hydra.dsl.Terms.list;
import static hydra.dsl.Terms.record;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class RewritingTest {
    private static final Name bboxName = new Name("BoundingBox");
    private static final Name geoPointName = new Name("GeoPoint");
    private static final Name stateGeoName = new Name("StateGeometry");

    private static final Term caBbox = annot("Bounding box for California",
            record(bboxName, field("southwest",
                            record(geoPointName, field("lat", float32(32.534156f)),
                                    field("lon", float32(-124.409591f)))),
                    field("northeast",
                            record(geoPointName,
                                    field("lat", float32(42.009518f)),
                                    field("lon", float32(-114.131211f))))));

    private static final Term caCapital = annot("Coordinates of Sacramento",
            record(geoPointName,
                    field("lat", float32(38.5816f)),
                    field("lon", annot("fail here", float32(-121.4944f)))));

    private static final Term caGeom = annot("Geometry of California",
            record(stateGeoName, field("boundingBox", caBbox), field("capital", caCapital)));

    private static final Term listOfStates = annot("A list of states", list(caGeom, caGeom, caGeom));

    @Test
    public void checkFailure() {
        FlowState<Integer, Term> resultState = applyFailOnSpecialAnnotation(listOfStates, 0);
        assertFalse(resultState.value.isPresent());
        assertEquals(1, resultState.trace.messages.size());
        assertTrue(resultState.trace.messages.get(0).startsWith("Error: "));
    }

    @Test
    public void checkSimpleRewritingScenarios() {
        FlowState<Integer, Term> resultState = applyCapitalizeFieldNames(listOfStates);

        // Check modified fields
        Opt<Term> result = resultState.value;
        assertTrue(result.isPresent());
        assertTrue(result.get() instanceof Term.Annotated);
        Term list = ((Term.Annotated) result.get()).value.subject;
        assertTrue(list instanceof Term.List);
        List<Term> vals = ((Term.List) list).value;
        assertEquals(3, vals.size());
        Term stateAnn = vals.get(2);
        assertTrue(stateAnn instanceof Term.Annotated);
        Term state = ((Term.Annotated) stateAnn).value.subject;
        assertTrue(state instanceof Term.Record);
        List<Field> fields = ((Term.Record) state).value.fields;
        assertEquals(2, fields.size());
        Field bboxfield = fields.get(0);
        assertEquals("BOUNDINGBOX", bboxfield.name.value);
        Field capitalField = fields.get(1);
        assertEquals("CAPITAL", capitalField.name.value);

        // Check modified state
        int pointFields = 2;
        int bboxFields = 2 + 2 * pointFields;
        int stateFields = 2 + pointFields + bboxFields;
        int listlen = 3;
        int totalFields = listlen * stateFields;
        assertEquals(Integer.valueOf(totalFields), resultState.state);
    }

    // Capitalizes record field names, and also counts the number of fields mutated
    private static  Flow<Integer, Term> capitalizeFieldNames(
            Function<Term, Flow<Integer, Term>> recurse,
            Term original) {
        return original.accept(new Term.PartialVisitor<Flow<Integer, Term>>() {
            @Override
            public Flow<Integer, Term> otherwise(Term instance) {
                Term inst = instance;
                return recurse.apply(inst);
            }

            @Override
            public Flow<Integer, Term> visit(Term.Record instance) {
                Record rec = instance.value;
                Flow<Integer, List<Field>> modFields = mapM(rec.fields, field -> bind(getState(),
                        count -> bind(putState(count + 1),
                                ignore -> map(capitalizeFieldNames(recurse, field.term),
                                term -> field(field.name.value.toUpperCase(), term)))));
                return map(modFields, fields -> new Term.Record(new Record(instance.value.typeName, fields)));
            }
        });
    }

    private static FlowState<Integer, Term> applyCapitalizeFieldNames(Term source) {
        Flow<Integer, Term> flow1 = rewriteTermM(recurse -> t -> capitalizeFieldNames(recurse, t),
                Flows::pure, source);
        return flow1.value.apply(0).apply(EMPTY_TRACE);
    }

    private static <S> Flow<S, Term> failOnSpecialAnnotation(
            Function<Term, Flow<S, Term>> recurse,
            Term original) {
        return original.accept(new Term.PartialVisitor<>() {
            @Override
            public Flow<S, Term> otherwise(Term instance) {
                return recurse.apply(instance);
            }

            @Override
            public Flow<S, Term> visit(Term.Annotated instance) {
                Map<Name, Term> mp = instance.value.annotation;
                assertEquals(1, mp.size());
                Term desc = mp.get(new Name("description"));
                assertNotNull(desc);
                if (desc.equals(Terms.string("fail here"))) {
                    return Flows.fail("failed");
                } else {
                    return recurse.apply(instance);
                }
            }
        });
    }

    private static <S> FlowState<S, Term> applyFailOnSpecialAnnotation(Term source, S seed) {
        Flow<S, Term> flow1 = rewriteTermM(
                recurse -> t -> failOnSpecialAnnotation(recurse, t), Flows::pure, source);
        return flow1.value.apply(seed).apply(EMPTY_TRACE);
    }
}
