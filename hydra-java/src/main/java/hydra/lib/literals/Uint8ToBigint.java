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

public class Uint8ToBigint extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.uint8ToBigint");
    }

    @Override
    public Type type() {
        return function(Types.uint8(), Types.bigint());
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.uint8(args.get(0)), s -> Terms.bigint(apply(s)));
    }

    public static BigInteger apply(Byte value) {
        return BigInteger.valueOf(value);
    }
}
