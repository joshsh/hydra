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

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.set;


public class Remove extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/sets.remove");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", function("x", set("x")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.set(Flows::pure, args.get(1)), arg -> Terms.set(apply(args.get(0), arg)));
    }

    public static <X> Function<Set<X>, Set<X>> apply(X elem) {
        return (arg) -> apply(elem, arg);
    }

    /**
     * Apply the function to both arguments.
     */
    public static <X> Set<X> apply(X elem, Set<X> arg) {
        Set<X> newSet = new HashSet<>(arg);
        newSet.remove(elem);
        return newSet;
    }
}
