package hydra.lib.sets;

import hydra.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.Type;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.lambda;
import static hydra.dsl.Types.set;

public class Difference extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/sets.difference");
    }

    @Override
    public Type type() {
        return lambda("x", function(set("x"), set("x"), set("x")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map2(
                Expect.set(Flows::pure, args.get(0)),
                Expect.set(Flows::pure, args.get(1)),
                (s1, s2) -> Terms.set(apply(s1, s2)));
    }

    public static <X> Function<Set<X>, Set<X>> apply(Set<X> s1) {
        return (s2) -> apply(s1, s2);
    }

    /**
     * Apply the function to both arguments.
     */
    public static <X> Set<X> apply(Set<X> s1, Set<X> s2) {
        Set<X> newSet = new HashSet<>(s1);
        newSet.removeAll(s2);
        return newSet;
    }
}
