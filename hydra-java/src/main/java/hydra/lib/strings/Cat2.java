package hydra.lib.strings;

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
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;

public class Cat2 extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/strings.cat2");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(string(), string(), string()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map2(
                Expect.string(args.get(0)),
                Expect.string(args.get(1)),
            (l, r) -> Terms.string(Cat2.apply(l, r)));
    }

    public static String apply(String left, String right) {
        return left + right;
    }
}
