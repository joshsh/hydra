package hydra.lib.literals;

import hydra.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.Type;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.dsl.Types;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.math.BigInteger;
import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;

public class BigintToInt64 extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.bigintToInt64");
    }

    @Override
    public Type type() {
        return function(Types.bigint(), Types.int64());
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.bigint(args.get(0)), s -> Terms.int64(apply(s)));
    }

    public static Long apply(BigInteger value) {
        return value.longValue();
    }
}
