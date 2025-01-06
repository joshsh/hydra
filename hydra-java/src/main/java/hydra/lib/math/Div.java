package hydra.lib.math;

import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import static hydra.dsl.Flows.bind2;
import static hydra.dsl.Flows.fail;
import static hydra.dsl.Flows.pure;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.int32;
import static hydra.dsl.Types.scheme;

public class Div extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/math.div");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(int32(), int32(), int32()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> bind2(Expect.int32(args.get(0)), Expect.int32(args.get(1)),
            (BiFunction<Integer, Integer, Flow<Graph, Term>>) (arg0, arg1) -> {
                if (arg1.equals(0)) {
                    return fail("division by zero");
                } else {
                    return pure(Terms.int32(apply(arg0, arg1)));
                }
            });
    }

    public static Function<Integer, Integer> apply(Integer dividend) {
        return (divisor) -> apply(dividend, divisor);
    }

    public static Integer apply(Integer dividend, Integer divisor) {
        return (dividend / divisor);
    }
}
