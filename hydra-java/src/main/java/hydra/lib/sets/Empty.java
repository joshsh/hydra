package hydra.lib.sets;

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
import java.util.Set;
import java.util.function.Function;

import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.set;


public class Empty extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/sets.empty");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", set("x"));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return ignored -> Flows.pure(Terms.set(apply()));
    }

    public static <X> Set<X> apply() {
        return Collections.emptySet();
    }
}
