package hydra.lib.logic;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.boolean_;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;


public class IfElse extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/logic.ifElse");
    }

    @Override
    public TypeScheme type() {
        return scheme("a",
            function("a", "a", function(boolean_(), "a")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.boolean_(args.get(2)), b -> IfElse.apply(args.get(0), args.get(1), b));
    }

    public static <X> Function<X, Function<Boolean, X>> apply(X ifBranch) {
        return elseBranch -> condition -> apply(ifBranch, elseBranch, condition);
    }

    public static <X> Function<Boolean, X> apply(X ifBranch, X elseBranch) {
        return condition -> IfElse.apply(ifBranch, elseBranch, condition);
    }

    public static <X> X apply(X ifBranch, X elseBranch, boolean condition) {
        return condition ? ifBranch : elseBranch;
    }
}
