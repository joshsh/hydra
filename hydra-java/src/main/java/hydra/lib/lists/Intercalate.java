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


public class Intercalate extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/lists.intercalate");
    }

    @Override
    public TypeScheme type() {
        return scheme("a",
                function(list("a"), list(list("a")), list("a")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map2(
            Expect.list(Flows::pure, args.get(0)),
            Expect.list(t -> Expect.list(Flows::pure, t), args.get(1)),
            (delim1, sublists1) -> Terms.list(apply(delim1, sublists1)));
    }

    public static <X> Function<List<List<X>>, List<X>> apply(List<X> delim) {
        return (sublists) -> apply(delim, sublists);
    }

    /**
     * Apply the function to both arguments.
     */
    public static <X> List<X> apply(List<X> delim, List<List<X>> sublists) {
        List<X> result = new ArrayList<>();
        boolean first = true;
        for (List<X> sublist : sublists) {
            if (first) {
                first = false;
            } else {
                result.addAll(delim);
            }
            result.addAll(sublist);
        }
        return result;
    }
}
