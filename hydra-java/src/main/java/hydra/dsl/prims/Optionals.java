package hydra.dsl.prims;

import hydra.core.Term;
import hydra.lib.optionals.Apply;
import hydra.lib.optionals.Bind;
import hydra.lib.optionals.Map;
import hydra.lib.optionals.Pure;

public interface Optionals {
    static <A> Term<A> apply() {
        return new Apply().term();
    }

    static <A> Term<A> bind() {
        return new Bind().term();
    }

    static <A> Term<A> map() {
        return new Map().term();
    }

    static <A> Term<A> pure() {
        return new Pure().term();
    }
}
