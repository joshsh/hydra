package hydra.lib.lists;

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
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.scheme;

public class Cons extends PrimitiveFunction {
    public static final Name NAME = new Name("hydra/lib/lists.cons");

    public Name name() {
        return NAME;
    }

    @Override
    public TypeScheme type() {
        return scheme("a", function("a", list("a"), list("a")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(
                Expect.list(Flows::pure, args.get(1)),
                l -> Terms.list(Cons.apply(args.get(0), l)));
    }

    /**
     * Apply the function to both arguments.
     */
    public static <X> List<X> apply(X el, List<X> l) {
        List<X> combined = new ArrayList<>();
        combined.add(el);
        combined.addAll(l);
        return combined;
    }
}
