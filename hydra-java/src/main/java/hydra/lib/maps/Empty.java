package hydra.lib.maps;

import hydra.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.Type;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static hydra.dsl.Types.lambda;
import static hydra.dsl.Types.map;

public class Empty extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/maps.empty");
    }

    @Override
    public Type type() {
        return lambda("k", "v", map("k", "v"));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return ignored -> Flows.pure(Terms.map(apply()));
    }

    public static <K, V> Map<K, V> apply() {
        return Collections.emptyMap();
    }
}
