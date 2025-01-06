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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.map;
import static hydra.dsl.Types.scheme;

public class Keys extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/maps.keys");
    }

    @Override
    public TypeScheme type() {
        return scheme("k", "v",
                function(
                        map("k", "v"),
                        list("k")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> {
            Flow<Graph, Map<Term, Term>> r = Expect.map(Flows::pure, Flows::pure, args.get(0));
            return Flows.map(r, map -> Terms.list(apply(map)));
        };
    }

    public static <K, V> List<K> apply(Map<K, V> map) {
        return new ArrayList<K>(map.keySet());
    }
}
