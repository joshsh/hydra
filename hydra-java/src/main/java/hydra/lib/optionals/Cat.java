package hydra.lib.optionals;

import hydra.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.Type;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.ArrayList;
import java.util.List;
import hydra.util.Opt;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.lambda;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.optional;


public class Cat extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/optionals.cat");
    }

    @Override
    public Type type() {
        return lambda("a", function(list(optional("a")), list("a")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.list(x -> Expect.optional(Flows::pure, x), args.get(0)),
                (Function<List<Opt<Term>>, Term>) optionals -> Terms.list(apply(optionals)));
    }

    /**
     * Apply the function to its single argument.
     */
    public static <X> List<X> apply(List<Opt<X>> opt) {
        List<X> result = new ArrayList<>();
        for (Opt<X> x : opt) {
            x.ifPresent(result::add);
        }
        return result;
    }
}
