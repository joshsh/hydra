package hydra;

import hydra.compute.Flow;
import hydra.core.Name;
import hydra.dsl.Flows;
import hydra.graph.Graph;
import hydra.graph.Primitive;

import hydra.util.Opt;

import static hydra.dsl.Flows.bind;
import static hydra.dsl.Flows.fail;
import static hydra.dsl.Flows.getState;


/**
 * Lexical functions (which deal with named elements and primitives within graphs).
 */
public class Lexical {
    private Lexical() {
    }

    /**
     * Get a primitive from a graph by name; the primitive is not required to exist.
     */
    public static  Opt<Primitive> lookupPrimitive(Graph g, Name name) {
        return Opt.ofNullable(g.primitives.get(name));
    }

    /**
     * Get a primitive from the current graph by name; the primitive is required to exist.
     */
    public static  Flow<Graph, Primitive> requirePrimitive(Name name) {
        return bind(getState(), g -> {
            Opt<Primitive> mprim = lookupPrimitive(g, name);
            return mprim.<Flow<Graph, Primitive>>map(Flows::pure)
                .orElseGet(() -> fail("no such primitive function: " + name.value));
        });
    }
}
