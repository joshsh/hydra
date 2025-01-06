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
import hydra.util.Tuple;

import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.map;
import static hydra.dsl.Types.pair;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.variable;


public class ToList extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/maps.toList");
    }

    @Override
    public TypeScheme type() {
        return scheme("k", "v", function(
                map("k", "v"),
                list(pair(variable("k"), variable("v")))));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> {
            Flow<Graph, Map<Term, Term>> r = Expect.map(Flows::pure, Flows::pure, args.get(0));
            return Flows.map(r, map -> Terms.list(apply(map).stream().map(Terms::pair).collect(Collectors.toList())));
        };
    }

    /**
     * Apply the function to its single argument.
     */
    public static <K, V> List<Tuple.Tuple2<K, V>> apply(Map<K, V> map) {
        List<Tuple.Tuple2<K, V>> pairs = new java.util.ArrayList<>(map.size());
        for (Map.Entry<K, V> entry : map.entrySet()) {
            pairs.add(new Tuple.Tuple2<>(entry.getKey(), entry.getValue()));
        }
        return pairs;
    }
}
