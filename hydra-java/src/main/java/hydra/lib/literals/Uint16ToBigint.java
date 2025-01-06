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

public class Uint16ToBigint extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.uint16ToBigint");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(Types.uint16(), Types.bigint()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.uint16(args.get(0)), s -> Terms.bigint(apply(s)));
    }

    public static BigInteger apply(Character value) {
        return BigInteger.valueOf(value);
    }
}
