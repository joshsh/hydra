package hydra;

import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.core.Term;
import hydra.graph.Graph;
import hydra.test.testSuite.TestSuite;
import hydra.testing.TestCase;
import hydra.testing.TestGroup;
import hydra.tools.PrettyPrinter;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.List;

import static hydra.dsl.Flows.EMPTY_TRACE;
import static org.junit.jupiter.api.Assertions.assertEquals;


/**
 * Java executor for Hydra's language-agnostic test suite.
 */
public class TestSuiteRunner extends HydraTestBase {

    @ParameterizedTest
    @MethodSource("provideTestCases")
    void runParameterizedTestCase(String name, Term input, Term output) {
        runReductionTestCase(true, name, input, output);
    }

    /**
     * Run a beta-reduction test case.
     */
    public static void runReductionTestCase(boolean eager, String name, Term input, Term output) {
        Graph graph = emptyGraph();
        String suffix = " (" + name + ")";

        Flow<Graph, Term> reduced = Reduction.reduce(eager, input);
        FlowState<Graph, Term> result = reduced.value.apply(graph).apply(EMPTY_TRACE);
        if (result.value.isPresent()) {
            if (!result.value.get().equals(output)) {
                // First, assert that the pretty-printed strings for the results are the same;
                // this provides more readable failure messages.
                assertEquals(print(output), print(result.value.get()),
                        "Original term does not reduce to expected term" + suffix);
                // Now check that the terms are truly equal
                assertEquals(output, result.value.get(), "Original term does not reduce to expected term" + suffix);
            }
        } else if (result.trace.messages.isEmpty()) {
            Assertions.fail("Reduction failed" + suffix);
        } else {
            Assertions.fail("Reduction failed: " + result.trace.messages.get(0) + suffix);
        }
    }

    private static String print(Term term) {
        return PrettyPrinter.printTerm(term);
    }

    private static List<Arguments> provideTestCases() {
        List<Arguments> args = new ArrayList<>();
        addTestGroup(TestSuite.allTests(), null, args);
        return args;
    }

    private static void addTestCase(TestCase testCase, int idx, String prefix, List<Arguments> args) {
        args.add(Arguments.of(testCaseDescription(testCase, prefix, idx), testCase.input, testCase.output));
    }

    private static void addTestGroup(TestGroup testGroup, String prefix, List<Arguments> args) {
        String newPrefix = testGroupDescription(testGroup, prefix);
        int idx = 0;
        for (TestCase testCase : testGroup.cases) {
            addTestCase(testCase, ++idx, newPrefix, args);
        }
        for (TestGroup subgroup : testGroup.subgroups) {
            addTestGroup(subgroup, newPrefix, args);
        }
    }

    private static String testCaseDescription(TestCase testCase, String prefix, int idx) {
        String name = testCase.description.orElse("test #" + idx);
        return prefix == null ? name : prefix + " > " + name;
    }

    private static String testGroupDescription(TestGroup testGroup, String prefix) {
        String name = testGroup.name + testGroup.description.map(s -> " (" + s + ")").orElse("");
        return prefix == null ? name : prefix + " > " + name;
    }
}
