package hydra.dsl;

import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.core.Unit;
import hydra.util.Opt;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static hydra.dsl.Flows.EMPTY_TRACE;
import static hydra.dsl.Flows.MAX_MAPM_SIZE;
import static hydra.dsl.Flows.UNIT;
import static hydra.dsl.Flows.bind;
import static hydra.dsl.Flows.getState;
import static hydra.dsl.Flows.map;
import static hydra.dsl.Flows.mapM;
import static hydra.dsl.Flows.pure;
import static hydra.dsl.Flows.putState;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class FlowsTest {
    @Test
    public void checkFail() {
        Flow<String, Integer> flow1 = Flows.fail("oops");
        FlowState<String, Integer> result1 = flow1.value.apply("").apply(EMPTY_TRACE);
        assertFalse(result1.value.isPresent());
        assertEquals(1, result1.trace.messages.size());
        assertEquals("Error: oops", result1.trace.messages.get(0));

        Function<String, Flow<Boolean, Integer>> nonzeroLen =
            s -> s.length() > 0 ? pure(s.length()) : Flows.fail("zero");
        List<String> strings = Arrays.asList("one", "two", "", "four");
        Flow<Boolean, List<Integer>> flow2 = mapM(strings, nonzeroLen);
        FlowState<Boolean, List<Integer>> result2 = flow2.value.apply(true).apply(EMPTY_TRACE);
        assertFalse(result2.value.isPresent());
    }

    @Test
    public void checkGetAndPutState() {
        Flow<Integer, Integer> flow1 = bind(pure(42), value -> map(getState(), state -> value + state));
        FlowState<Integer, Integer> result1 = flow1.value.apply(10).apply(EMPTY_TRACE);
        assertTrue(result1.value.isPresent());
        assertEquals(52, result1.value.get());

        Flow<Integer, Integer> flow2 = bind(pure(42), original -> bind(putState(100), ignored -> pure(original)));
        FlowState<Integer, Integer> result2 = flow2.value.apply(10).apply(EMPTY_TRACE);
        assertTrue(result2.value.isPresent());
        assertEquals(42, result2.value.get());
        assertEquals(100, result2.state);

        Flow<String, Integer> flow3 = bind(pure(42), value -> bind(getState(), state -> {
            String newState = state + ";" + value;
            return bind(putState(newState), ignored -> pure(value + 1));
        }));
        FlowState<String, Integer> result3 = flow3.value.apply("foo").apply(EMPTY_TRACE);
        assertEquals("foo;42", result3.state);
        assertEquals(Opt.of(43), result3.value);
    }

    @Test
    public void checkMapMSizeLimitForLists() {
        List<Integer> list1 = Arrays.asList(1, 2, 3, 4, 5);
        List<Integer> list2 = new LinkedList<>();
        for (int i = 0; i <= MAX_MAPM_SIZE; i++) {
            list2.add(i);
        }

        // Small list succeeds
        assertEquals(5, Flows.fromFlow(mapM(list1, Flows::pure)).size());
        // Large list fails
        assertThrows(IllegalArgumentException.class, () -> Flows.mapM(list2, Flows::pure));
    }

    @Test
    public void checkMapMSizeLimitForMaps() {
        Map<Integer, Integer> map1 = Map.of(1, 1, 2, 2, 3, 3, 4, 4, 5, 5);
        Map<Integer, Integer> map2 = new HashMap<>();
        for (int i = 0; i <= MAX_MAPM_SIZE; i++) {
            map2.put(i, i);
        }

        // Small map succeeds
        assertEquals(5, Flows.fromFlow(mapM(map1, Flows::pure, Flows::pure)).size());
        // Large map fails
        assertThrows(IllegalArgumentException.class, () -> Flows.mapM(map2, Flows::pure, Flows::pure));
    }

    @Test
    public void checkMapMSizeLimitForSets() {
        Set<Integer> set1 = Set.of(1, 2, 3, 4, 5);
        Set<Integer> set2 = new HashSet<>();
        for (int i = 0; i <= MAX_MAPM_SIZE; i++) {
            set2.add(i);
        }

        // Small set succeeds
        assertEquals(5, Flows.fromFlow(mapM(set1, Flows::pure)).size());
        // Large set fails
        assertThrows(IllegalArgumentException.class, () -> Flows.mapM(set2, Flows::pure));
    }

    @Test
    public void checkWarnings() {
        final Flow<Unit, Integer> flow0 = pure(42);
        final Flow<Unit, Integer> flow1 = Flows.warn("oops", flow0);
        final Flow<Unit, Integer> flow2 = Flows.warn("drat", flow1);
        final Flow<Unit, Integer> flow3 = Flows.warn("oops", flow2);
        final Flow<Unit, Integer> flow4 = Flows.bind(flow3, x -> Flows.fail("failed"));

        final FlowState<Unit, Integer> result0 = flow0.value.apply(UNIT).apply(EMPTY_TRACE);
        final FlowState<Unit, Integer> result1 = flow1.value.apply(UNIT).apply(EMPTY_TRACE);
        final FlowState<Unit, Integer> result2 = flow2.value.apply(UNIT).apply(EMPTY_TRACE);
        final FlowState<Unit, Integer> result3 = flow3.value.apply(UNIT).apply(EMPTY_TRACE);
        final FlowState<Unit, Integer> result4 = flow4.value.apply(UNIT).apply(EMPTY_TRACE);

        assertTrue(result0.value.isPresent());
        assertTrue(result1.value.isPresent());
        assertTrue(result2.value.isPresent());
        assertTrue(result3.value.isPresent());
        assertFalse(result4.value.isPresent());

        assertEquals(0, result0.trace.messages.size());
        assertEquals(1, result1.trace.messages.size());
        assertEquals(2, result2.trace.messages.size());
        assertEquals(3, result3.trace.messages.size());
        assertEquals(4, result4.trace.messages.size());

        assertEquals("Warning: oops", result1.trace.messages.get(0));

        // Warning messages are FILO
        assertEquals("Warning: drat", result2.trace.messages.get(0));
        assertEquals("Warning: oops", result2.trace.messages.get(1));

        // Failure message appears at the end
        assertEquals("Warning: oops", result4.trace.messages.get(0));
        assertEquals("Warning: drat", result4.trace.messages.get(1));
        assertEquals("Warning: oops", result4.trace.messages.get(2));
        assertEquals("Error: failed", result4.trace.messages.get(3));
    }
}
