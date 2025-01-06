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
import java.util.function.BiFunction;
import java.util.function.Function;

import static hydra.dsl.Flows.map2;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.optional;
import static hydra.dsl.Types.scheme;


public class Apply extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/optionals.apply");
    }

    @Override
    public TypeScheme type() {
        return scheme("a", "b",
            function(optional(function("a", "b")), optional("a"), optional("b")));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> map2(Expect.optional(Flows::pure, args.get(0)), Expect.optional(Flows::pure, args.get(1)),
            (BiFunction<Opt<Term>, Opt<Term>, Term>) (optionalF, optionalArg) ->
                (optionalF.isPresent() && optionalArg.isPresent())
                    ? Terms.optional(Opt.of(Terms.apply(optionalF.get(), optionalArg.get())))
                    : Terms.optional(Opt.empty()));
    }

    public static <X, Y> Function<Opt<X>, Opt<Y>> apply(Opt<Function<X, Y>> optionalF) {
        return (optionalArg) -> apply(optionalF, optionalArg);
    }

    /**
     * Apply the function to both arguments.
     */
    public static <X, Y> Opt<Y> apply(Opt<Function<X, Y>> optionalF, Opt<X> optionalArg) {
        if (!optionalF.isPresent() || !optionalArg.isPresent()) {
            return Opt.empty();
        }

        Function<X, Y> f = optionalF.get();
        X arg = optionalArg.get();

        return Opt.of(f.apply(arg));
    }
}
