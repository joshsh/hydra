package hydra.lib.logic;

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
import java.util.function.Function;

import static hydra.dsl.Types.boolean_;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;


public class Not extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/logic.not");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(boolean_(), boolean_()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(
                Expect.boolean_(args.get(0)),
                b1 -> Terms.boolean_(Not.apply(b1)));
    }

    public static boolean apply(boolean b1) {
        return !b1;
    }
}
