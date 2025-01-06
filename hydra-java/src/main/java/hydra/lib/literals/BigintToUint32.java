package hydra.lib.literals;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.dsl.Types;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.math.BigInteger;
import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;

public class BigintToUint32 extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.bigintToUint32");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(Types.bigint(), Types.uint32()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.bigint(args.get(0)), s -> Terms.uint32(apply(s)));
    }

    public static Long apply(BigInteger value) {
        return value.longValue();
    }
}
