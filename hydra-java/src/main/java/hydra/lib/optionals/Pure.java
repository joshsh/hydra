package hydra.lib.optionals;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;
import hydra.util.Opt;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.optional;
import static hydra.dsl.Types.scheme;


public class Pure extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/optionals.pure");
    }

    @Override
    public TypeScheme type() {
        return scheme("a", function("a", optional("a")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.pure(Terms.optional(apply(args.get(0))));
    }

    public static <X> Opt<X> apply(X arg) {
        return Opt.of(arg);
    }
}
