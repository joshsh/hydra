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
import org.apache.commons.text.StringEscapeUtils;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;

public class ShowString extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/literals.showString");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(string(), string()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.map(Expect.string(args.get(0)), (Function<String, Term>) s -> Terms.string(apply(s)));
    }

    public static String apply(String value) {
        return "\"" + StringEscapeUtils.escapeJava(value) + "\"";
    }
}
