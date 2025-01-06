package hydra.lib.optionals;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;
import hydra.util.Opt;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.optional;
import static hydra.dsl.Types.scheme;


public class IsJust extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/optionals.isJust");
    }

    @Override
    public TypeScheme type() {
        return scheme("a", function(optional("a"), "a"));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.optional(Flows::pure, args.get(0)), x -> Terms.boolean_(IsJust.apply(x)));
    }

    public static <X> boolean apply(Opt<X> opt) {
        return opt.isPresent();
    }
}
