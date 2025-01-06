package hydra.lib.lists;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.scheme;


public class Pure extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/lists.pure");
    }

    @Override
    public TypeScheme type() {
        return scheme("a", function("a", list("a")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.pure(Terms.list(apply(args.get(0))));
    }

    /**
     * Apply the function to the single argument.
     */
    public static <X> List<X> apply(X single) {
        return Collections.singletonList(single);
    }
}
