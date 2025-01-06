package hydra.lib.lists;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Flows.map;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.scheme;

public class Last extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/lists.last");
    }

    @Override
    public TypeScheme type() {
        return scheme("a", function(list("a"), "a"));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> map(Expect.list(Flows::pure, args.get(0)), Last::apply);
    }

    public static <X> X apply(List<X> list) {
        return list.get(list.size() - 1);
    }
}
