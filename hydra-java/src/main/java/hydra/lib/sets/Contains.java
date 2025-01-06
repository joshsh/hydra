package hydra.lib.sets;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static hydra.dsl.Types.boolean_;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.set;


public class Contains extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/sets.contains");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", function("x", set("x"), boolean_()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.set(Flows::pure, args.get(1)),
            terms -> Terms.boolean_(apply(args.get(0), terms)));
    }

    public static <X> Function<Set<X>, Boolean> apply(X elem) {
        return (arg) -> apply(elem, arg);
    }

    public static <X> Boolean apply(X elem, Set<X> arg) {
        return arg.contains(elem);
    }
}
