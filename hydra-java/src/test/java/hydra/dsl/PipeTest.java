package hydra.dsl;

import hydra.compute.FlowState;
import hydra.core.Unit;
import hydra.tools.FlowException;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import org.junit.jupiter.api.Test;

import static hydra.dsl.Pipe.*;
import static org.junit.jupiter.api.Assertions.*;


/**
 * Note: some duplication w.r.t. FlowsTest
 */
public class PipeTest {
    private static final Function<String, String> capitalize = String::toUpperCase;
    private static final Function<String, Integer> strlen = String::length;
    private static final Function<Integer, Pipe<Double>> squareRoot = v -> v < 0
        ? Pipe.fail("square root of negative number")
        : Pipe.pure(Math.sqrt(v));

    @Test
    public void checkFluentSyntax() {
      assertEquals("abcd", new Pipe<>("abcd").eval());
      assertEquals("ABCD", new Pipe<>("abcd").map(capitalize).eval());
      assertEquals(4, new Pipe<>("abcd").map(capitalize).map(strlen).eval());
      assertEquals(2.0, new Pipe<>("abcd").map(capitalize).map(strlen).flatMap(squareRoot).eval());
    }

    @Test
    public void checkFail() {
        Pipe<Integer> pipe1 = Pipe.fail("oops");
        FlowState<Unit, Integer> result1 = pipe1.flow.value.apply(new Unit()).apply(Flows.EMPTY_TRACE);
        assertFalse(result1.value.isPresent());
        assertEquals(1, result1.trace.messages.size());
        assertEquals("Error: oops", result1.trace.messages.get(0));

        Function<String, Pipe<Integer>> nonzeroLen =
            s -> s.length() > 0 ? Pipe.pure(s.length()) : Pipe.fail("zero");
        List<String> strings = Arrays.asList("one", "two", "", "four");
        Pipe<List<Integer>> pipe2 = mapM(strings, nonzeroLen);
        FlowState<Unit, List<Integer>> result2 = pipe2.flow.value.apply(new Unit()).apply(Flows.EMPTY_TRACE);
        assertFalse(result2.value.isPresent());
    }

    @Test
    public void checkEvaluationFailure() {
        assertThrows(FlowException.class, () -> {
            new Pipe<>(-1).flatMap(squareRoot).eval();
        });
    }

    @Test
    public void checkWarnings() {
        Pipe<Integer> pipe1 = new Pipe<>(-1).warn("oops").warn("drat").warn("sigh");
        Pipe<Double> pipe2 = new Pipe<>(-1).warn("oops").warn("drat").warn("sigh").flatMap(squareRoot);
        FlowState<Unit, Integer> result1 = pipe1.flow.value.apply(Flows.UNIT).apply(Flows.EMPTY_TRACE);
        FlowState<Unit, Double> result2 = pipe2.flow.value.apply(Flows.UNIT).apply(Flows.EMPTY_TRACE);

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
