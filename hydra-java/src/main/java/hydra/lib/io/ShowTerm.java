package hydra.lib.io;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.TypeScheme;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.PrimitiveFunction;

import java.util.List;
import java.util.function.Function;

import static hydra.dsl.Types.function;
import static hydra.dsl.Types.scheme;
import static hydra.dsl.Types.string;
import static hydra.dsl.Types.variable;


public class ShowTerm extends PrimitiveFunction {
    public Name name() {
        return new Name("hydra/lib/io.showTerm");
    }

    @Override
    public TypeScheme type() {
        return scheme(function(variable(Term.TYPE_NAME), string()));
    }

    @Override
    protected Function<List<Term>, Flow<Graph, Term>> implementation() {
        return args -> Flows.pure(Terms.string(ShowTerm.apply(args.get(0))));
    }

    public static  String apply(Term term) {
        // TODO: temporary
        return term.toString();
    }
}
