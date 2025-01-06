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

public class Intersperse extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/lists.intersperse");
    }

    @Override
    public TypeScheme type() {
        return scheme("a", function("a", list("a"), list("a")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(
            Expect.list(Flows::pure, args.get(1)),
            list -> Terms.list(apply(args.get(0), list)));
    }

    public static <X> Function<List<X>, List<X>> apply(X delim) {
        return (list) -> apply(delim, list);
    }

    /**
     * Apply the function to both arguments.
     */
    public static <X> List<X> apply(X delim, List<X> list) {
        List<X> result = new ArrayList<>();
        boolean first = true;
        for (X a : list) {
            if (first) {
                first = false;
            } else {
                result.add(delim);
            }
            result.add(a);
        }
        return result;
    }
}
