package hydra.lib.maps;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.HashMap;
import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Flows.pure;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.map;
import static hydra.dsl.Types.scheme;


public class MapKeys extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/maps.mapKeys");
    }

    @Override
    public TypeScheme type() {
        return scheme("k1", "k2", "v",
            function(function("k1", "k2"), map("k1", "v"), map("k2", "v")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(
            Expect.map(k -> pure(Terms.apply(args.get(0), k)), Flows::pure, args.get(1)), Terms::map);
    }

    public static <K1, K2, V> Function<java.util.Map<K1, V>, java.util.Map<K2, V>> apply(Function<K1, K2> mapping) {
        return (arg) -> apply(mapping, arg);
    }

    /**
     * Apply the function to both arguments.
     */
    public static <K1, K2, V> java.util.Map<K2, V> apply(Function<K1, K2> mapping, java.util.Map<K1, V> arg) {
        java.util.Map<K2, V> result = new HashMap<>();
        for (java.util.Map.Entry<K1, V> e : arg.entrySet()) {
            result.put(mapping.apply(e.getKey()), e.getValue());
        }
        return result;
    }
}
