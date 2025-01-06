package hydra.lib.equality;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;

public class Identity extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/equality.identity");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", function("x", "x"));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.pure(args.get(0));
    }

    public static <X> X apply(X object) {
        return object;
    }
}
