package hydra.lib.maps;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;
import hydra.util.Tuple;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static hydra.dsl.Expect.list;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.map;
import static hydra.dsl.Types.pair;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.variable;

public class FromList extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/maps.fromList");
    }

    @Override
    public TypeScheme type() {
        return scheme("k", "v",
                function(list(pair(variable("k"), variable("v"))), map("k", "v")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(list(term -> Expect.pair(Flows::pure, Flows::pure, term), args.get(0)),
                (Function<List<Tuple.Tuple2<Term, Term>>, Term>) pairs -> new Term.Map(apply(pairs)));
    }

    /**
     * Apply the function to its single argument.
     */
    public static <K, V> Map<K, V> apply(List<Tuple.Tuple2<K, V>> pairs) {
        Map<K, V> mp = new HashMap<>();
        for (Tuple.Tuple2<K, V> pair : pairs) {
            mp.put(pair.object1, pair.object2);
        }
        return mp;
    }
}
