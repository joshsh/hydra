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
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;


public class Cat extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/strings.cat");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(list(string()), string()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.list(Expect::string, args.get(0)),
            strings -> Terms.string(apply(strings)));
    }

    public static String apply(List<String> args) {
        return String.join("", args);
    }
}
