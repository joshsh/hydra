package hydra.lib.strings;

import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Expect;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import static hydra.dsl.Flows.map2;
import static hydra.dsl.Types.function;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;


public class SplitOn extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/strings.splitOn");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(string(), string(), list(string())));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> map2(Expect.string(args.get(0)), Expect.string(args.get(1)),
            (BiFunction<String, String, Term>) (s, s2) -> Terms.listOfStrings(apply(s, s2)));
    }

    public static Function<String, List<String>> apply(String delim) {
        return (string) -> apply(delim, string);
    }

    /**
     * Apply the function to both arguments.
     * Note: the delimiter is not interpreted as a regular expression;
     * it is simply a literal string. See Haskell's Data.List.Split.
     * */
    public static List<String> apply(String delim, String string) {
        List<String> parts = new ArrayList<>();

        if (delim.length() == 0) {
            parts.add("");
            for (int i = 0; i < string.length(); i++) {
                parts.add(string.substring(i, i + 1));
            }
        } else {
            byte[] delimBytes = delim.getBytes();
            byte[] stringBytes = string.getBytes();

            int k = 0;
            for (int i = 0; i <= stringBytes.length - delimBytes.length; i++) {
                boolean match = true;

                for (int j = 0; j < delimBytes.length; j++) {
                    if (stringBytes[i + j] != delimBytes[j]) {
                        match = false;
                        break;
                    }
                }

                if (match) {
                    parts.add(string.substring(k, i));
                    i += delimBytes.length;
                    k = i;
                    i--;
                }
            }

            parts.add(string.substring(k));
        }

        return parts;
    }
}
