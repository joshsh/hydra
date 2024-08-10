package hydra.lib.literals;

import hydra.Flows;
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

public class BigfloatToFloat32 extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.bigfloatToFloat32");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(Types.bigfloat(), Types.float32()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.bigfloat(args.get(0)), s -> Terms.float32(apply(s)));
    }

    public static Float apply(Double value) {
        return (float) ((double) value);
    }
}
