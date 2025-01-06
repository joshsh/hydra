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

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;

public class Float64ToBigfloat extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.float64ToBigfloat");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(Types.float64(), Types.bigfloat()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.float64(args.get(0)), s -> Terms.bigfloat(apply(s)));
    }

    public static Double apply(Double value) {
        return value;
    }
}
