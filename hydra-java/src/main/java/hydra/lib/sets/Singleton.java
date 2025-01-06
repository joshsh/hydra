package hydra.lib.sets;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
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


public class Singleton extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/sets.singleton");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", function("x", set("x")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.pure(Terms.set(apply(args.get(0))));
    }

    /**
     * Apply the function to its single argument.
     */
    public static <X> Set<X> apply(X elem) {
        Set<X> newSet = new HashSet<>();
        newSet.add(elem);
        return newSet;
    }
}
