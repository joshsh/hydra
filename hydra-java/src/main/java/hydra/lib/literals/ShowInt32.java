package hydra.lib.literals;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;
import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.int32;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;


public class ShowInt32 extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.showInt32");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(int32(), string()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.int32(args.get(0)), (Function<Integer, Term>) s -> Terms.string(apply(s)));
    }

    public static String apply(Integer value) {
        return Integer.toString(value);
    }
}
