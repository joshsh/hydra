package hydra.lib.strings;

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

import static hydra.dsl.Flows.map2;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;

public class Intercalate extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/strings.intercalate");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(string(), list(string()), string()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> map2(
                Expect.string(args.get(0)),
                Expect.list(Expect::string, args.get(1)),
                (delim, strings) -> Terms.string(Intercalate.apply(delim, strings)));
    }

    public static Function<List<String>, String> apply(String delim) {
        return (strings) -> apply(delim, strings);
    }

    /**
     * Apply the function to both arguments.
     */
    public static String apply(String delim, List<String> strings) {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (String s : strings) {
            if (first) {
                first = false;
            } else {
                sb.append(delim);
            }
            sb.append(s);
        }
        return sb.toString();
    }
}
