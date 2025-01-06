package hydra;

import hydra.compute.Coder;
import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.core.Unit;
import hydra.dsl.Flows;
import hydra.dsl.Terms;
import hydra.graph.Element;
import hydra.graph.Graph;
import hydra.graph.Primitive;
import hydra.lib.Libraries;
import hydra.tools.PrimitiveFunction;
import hydra.util.Opt;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Consumer;

import static hydra.Coders.*;
import static hydra.dsl.Flows.*;
import static org.junit.jupiter.api.Assertions.*;


public class HydraTestBase {

    protected static <S, X> void assertFails(Flow<S, X> flow, S initialState) {
        FlowState<S, X> result = flow.value.apply(initialState).apply(EMPTY_TRACE);
        assertTrue(!result.value.isPresent());
        //assertTrue(result.trace.messages.size() > 1);
    }

    protected static <X> void assertFails(Flow<Unit, X> flow) {
        assertFails(flow, Flows.UNIT);
    }

    protected static <V1, V2> void assertRoundTripIsNoop(Coder<Unit, Unit, V1, V2> coder, V1 initialValue) {
        assertRoundTripIsNoop(coder, new Unit(), initialValue);
    }

    protected static <S, V1, V2> void assertRoundTripIsNoop(Coder<S, S, V1, V2> coder,
                                                            S initialState,
                                                            V1 initialValue) {
        assertSucceedsWith(initialValue, roundTrip(coder, initialValue), initialState);
    }

    protected static <V1, V2> void assertRoundTripFails(Coder<Unit, Unit, V1, V2> coder, V1 initialValue) {
        assertFails(roundTrip(coder, initialValue));
    }

    protected static <S, V1, V2> void assertRoundTripFails(Coder<S, S, V1, V2> coder,
                                                           S initialState,
                                                           V1 initialValue) {
        assertFails(roundTrip(coder, initialValue), initialState);
    }

    protected static <S, X> void assertSucceeds(Flow<S, X> flow, S initialState) {
        checkFlow(flow, initialState, x -> assertTrue(true));
    }

    protected static <X> void assertSucceeds(Flow<Unit, X> flow) {
        assertSucceeds(flow, new Unit());
    }

    protected static <X> void assertSucceedsWith(X expected, Flow<Unit, X> flow) {
        assertSucceedsWith(expected, flow, new Unit());
    }

    protected static <S, X> void assertSucceedsWith(X expected, Flow<S, X> flow, S initialState) {
        checkFlow(flow, initialState, x -> assertEquals(expected, x));
    }

    protected static <S, X> void checkFlow(Flow<S, X> flow, S initialState, Consumer<X> consumer) {
        FlowState<S, X> result = flow.value.apply(initialState).apply(EMPTY_TRACE);
        assertTrue(result.value.isPresent(), "Flow failed: " + result.trace.messages);
        consumer.accept(result.value.get());
    }

    protected static <X> void checkFlow(Flow<Unit, X> flow, Consumer<X> consumer) {
        checkFlow(flow, new Unit(), consumer);
    }

    protected static  Graph emptyGraph() {
        Map<Name, Element> elements = Collections.emptyMap();
        Map<Name, TypeScheme> types = Collections.emptyMap();
        Map<Name, Opt<Term>> environment = Collections.emptyMap();
        Term body = Terms.string("empty graph");

        Map<Name, Primitive> primitives = new HashMap<>();
        for (PrimitiveFunction prim : Libraries.standardPrimitives()) {
            primitives.put(prim.name(), prim.toNative());
        }

        Opt<Graph> schema = Opt.empty();

        return new Graph(elements, environment, types, body, primitives, schema);
    }
}
