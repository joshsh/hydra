package hydra.dsl;

import hydra.compute.FlowState;
import hydra.core.Unit;
import hydra.tools.FlowException;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import org.junit.jupiter.api.Test;

import static hydra.dsl.Possible.*;
import static org.junit.jupiter.api.Assertions.*;


/**
 * Note: some duplication w.r.t. FlowsTest
 */
public class PossibleTest {
    private static final Function<String, String> capitalize = String::toUpperCase;
    private static final Function<String, Integer> strlen = String::length;
    private static final Function<Integer, Possible<Double>> squareRoot = v -> v < 0
        ? Possible.fail("square root of negative number")
        : Possible.pure(Math.sqrt(v));

    @Test
    public void checkFluentSyntax() {
      assertEquals("abcd", new Possible<>("abcd").eval());
      assertEquals("ABCD", new Possible<>("abcd").map(capitalize).eval());
      assertEquals(4, new Possible<>("abcd").map(capitalize).map(strlen).eval());
      assertEquals(2.0, new Possible<>("abcd").map(capitalize).map(strlen).flatMap(squareRoot).eval());
    }

    @Test
    public void checkFail() {
        Possible<Integer> possible1 = Possible.fail("oops");
        FlowState<Unit, Integer> result1 = possible1.flow.value.apply(new Unit()).apply(Flows.EMPTY_TRACE);
        assertFalse(result1.value.isPresent());
        assertEquals(1, result1.trace.messages.size());
        assertEquals("Error: oops", result1.trace.messages.get(0));

        Function<String, Possible<Integer>> nonzeroLen =
            s -> s.length() > 0 ? Possible.pure(s.length()) : Possible.fail("zero");
        List<String> strings = Arrays.asList("one", "two", "", "four");
        Possible<List<Integer>> possible2 = mapM(strings, nonzeroLen);
        FlowState<Unit, List<Integer>> result2 = possible2.flow.value.apply(new Unit()).apply(Flows.EMPTY_TRACE);
        assertFalse(result2.value.isPresent());
    }

    @Test
    public void checkEvaluationFailure() {
        assertThrows(FlowException.class, () -> {
            new Possible<>(-1).flatMap(squareRoot).eval();
        });
    }

    @Test
    public void checkWarnings() {
        Possible<Integer> possible1 = new Possible<>(-1).warn("oops").warn("drat").warn("sigh");
        Possible<Double> possible2 = new Possible<>(-1).warn("oops").warn("drat").warn("sigh").flatMap(squareRoot);
        FlowState<Unit, Integer> result1 = possible1.flow.value.apply(Flows.UNIT).apply(Flows.EMPTY_TRACE);
        FlowState<Unit, Double> result2 = possible2.flow.value.apply(Flows.UNIT).apply(Flows.EMPTY_TRACE);

        assertTrue(result1.value.isPresent());
        assertFalse(result2.value.isPresent());
        assertEquals(3, result1.trace.messages.size());
        assertEquals(4, result2.trace.messages.size());

        // Warning messages are FILO
        assertEquals("Warning: sigh", result1.trace.messages.get(0));
        assertEquals("Warning: sigh", result2.trace.messages.get(0));
        assertEquals("Warning: oops", result1.trace.messages.get(2));
        assertEquals("Warning: oops", result2.trace.messages.get(2));
        // Failure message appears at the end
        assertEquals("Error: square root of negative number", result2.trace.messages.get(3));
    }
}
