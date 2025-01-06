package hydra.lib.sets;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static hydra.dsl.Types.boolean_;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.set;


public class IsEmpty extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/sets.isEmpty");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", function(set("x"), boolean_()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.set(Flows::pure, args.get(0)), arg -> Terms.boolean_(apply(arg)));
    }

    public static <X> Boolean apply(Set<X> arg) {
        return arg.isEmpty();
    }
}
