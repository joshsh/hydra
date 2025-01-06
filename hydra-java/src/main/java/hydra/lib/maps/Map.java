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
import static hydra.dsl.Types.lambda;
import static hydra.dsl.Types.map;
import static hydra.dsl.Types.scheme;


public class Map extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/maps.map");
    }

    @Override
    public TypeScheme type() {
        return scheme("k", lambda("v1", lambda("v2",
            function(function("v1", "v2"), map("k", "v1"), map("k", "v2")))));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(
            Expect.map(Flows::pure, v -> pure(Terms.apply(args.get(0), v)), args.get(1)), Terms::map);
    }

    public static <K, V1, V2> Function<java.util.Map<K, V1>, java.util.Map<K, V2>> apply(Function<V1, V2> mapping) {
        return (arg) -> apply(mapping, arg);
    }

    /**
     * Apply the function to both arguments.
     */
    public static <K, V1, V2> java.util.Map<K, V2> apply(Function<V1, V2> mapping, java.util.Map<K, V1> arg) {
        java.util.Map<K, V2> result = new HashMap<>();
        for (java.util.Map.Entry<K, V1> e : arg.entrySet()) {
            result.put(e.getKey(), mapping.apply(e.getValue()));
        }
        return result;
    }
}
