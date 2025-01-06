package hydra.lib.flows;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Types;
import hydra.dsl.prims.Optionals;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Terms.app;
import static hydra.dsl.Terms.flowState;
import static hydra.dsl.Terms.lambda;
import static hydra.dsl.Terms.project;
import static hydra.dsl.Terms.unwrap;
import static hydra.dsl.Terms.variable;


public class Map extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/flows.map");
    }

    @Override
    public TypeScheme type() {
        return Types.scheme("s", "x", "y",
                Types.function(Types.function("x", "y"), Types.flow("s", "x"), Types.flow("s", "y")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> {
            Term mapping = args.get(0);
            Term input = args.get(1);
            Term output = lambda("s", "t",
                    app(lambda("q", flowState(
                                    app(Optionals.map(), mapping, app(project(FlowState.TYPE_NAME, "value"), variable("q"))),
                                    app(project(FlowState.TYPE_NAME, "state"), variable("q")),
                                    app(project(FlowState.TYPE_NAME, "trace"), variable("q")))),
                            (app(unwrap(Flow.TYPE_NAME), input, variable("s"), variable("t")))));
            return Flows.pure(output);
        };
    }

    public static <S, X, Y> Function<Flow<S, X>, Flow<S, Y>> apply(Function<X, Y> mapping) {
        return input -> apply(mapping, input);
    }

    public static <S, X, Y> Flow<S, Y> apply(Function<X, Y> mapping, Flow<S, X> input) {
        return Flows.map(mapping, input);
    }
}
