package hydra.lib.equality;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.boolean_;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;


public class Equal extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/equality.equal");
    }

    @Override
    public TypeScheme type() {
        return scheme("x", function("x", "x", boolean_()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        // Term equality is sufficient here, as we assume that type inference has already succeeded.
        return args -> Flows.pure(Terms.boolean_(args.get(0).equals(args.get(1))));
    }

    public static <A> Function<A, Boolean> apply(A left) {
        return right -> apply(left, right);
    }

    public static <A> boolean apply(A left, A right) {
        return left.equals(right);
    }
}
