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
import java.util.stream.Collectors;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.set;


public class Map extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/sets.map");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", "y",
                function(function("x", "y"), set("x"), set("y")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> {
            Term mapping = args.get(0);
            return Flows.map(Expect.set(Flows::pure, args.get(1)),
                arg -> Terms.set(arg.stream().map(e -> Terms.apply(mapping, e)).collect(Collectors.toSet())));
        };
    }

    public static <X, Y> Function<Set<X>, Set<Y>> apply(Function<X, Y> mapping) {
        return (arg) -> apply(mapping, arg);
    }

    public static <X, Y> Set<Y> apply(Function<X, Y> mapping, Set<X> arg) {
        return arg.stream().map(mapping).collect(Collectors.toSet());
    }
}
