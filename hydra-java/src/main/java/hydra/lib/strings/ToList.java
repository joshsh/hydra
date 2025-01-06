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

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.int32;
import static hydra.dsl.Types.list;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;

public class ToList extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/strings.toList");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(string(), list(int32())));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.string(args.get(0)), (Function<String, Term>) s -> {
            List<Integer> list = apply(s);
            List<Term> terms = new ArrayList<>(list.size());
            for (Integer i : list) {
                terms.add(Terms.int32(i));
            }
            return Terms.list(terms);
        });
    }

    /**
     * Apply the function to its single argument.
     */
    public static List<Integer> apply(String s) {
        List<Integer> list = new ArrayList<>(s.length());
        for (char c : s.toCharArray()) {
            list.add((int) c);
        }
        return list;
    }
}
