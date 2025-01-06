package hydra;

import hydra.compute.Adapter;
import hydra.compute.Flow;
import hydra.compute.StatelessAdapter;
import hydra.core.Unit;

import hydra.dsl.Flows;
import java.util.function.Function;

/**
 * Convenience functions for working with Hydra coders.
 */
public class Adapters {
    /**
     * Compose two adapters, in turn composing their coders.
     */
    public static <S1, S2, T1, T2, T3, V1, V2, V3> Adapter<S1, S2, T1, T3, V1, V3> compose(
            Adapter<S1, S2, T1, T2, V1, V2> adapter1,
            Adapter<S1, S2, T2, T3, V2, V3> adapter2) {

        return new Adapter<>(
                adapter1.isLossy || adapter2.isLossy,
                adapter1.source,
                adapter2.target,
                Coders.compose(adapter1.coder, adapter2.coder));
    }

    /**
     * Compose two adapters constructed from their source types, in turn composing their coders.
     */
    public static <S0, S1, S2, T1, T2, T3, V1, V2, V3> Function<T1, Flow<S0, Adapter<S1, S2, T1, T3, V1, V3>>> compose(
            Function<T1, Flow<S0, Adapter<S1, S2, T1, T2, V1, V2>>> constructor1,
            Function<T2, Flow<S0, Adapter<S1, S2, T2, T3, V2, V3>>> constructor2) {
        return t1 -> Flows.bind(
                constructor1.apply(t1),
                firstMile -> Flows.map(
                        constructor2.apply(firstMile.target),
                        lastMile -> compose(firstMile, lastMile)));
    }

    /**
     * Compose two stateless adapters, in turn composing their coders.
     */
    public static <T1, T2, T3, V1, V2, V3> StatelessAdapter<T1, T3, V1, V3> composeStateless(
            StatelessAdapter<T1, T2, V1, V2> adapter1,
            StatelessAdapter<T2, T3, V2, V3> adapter2) {

        return new StatelessAdapter<>(
                adapter1.isLossy || adapter2.isLossy,
                adapter1.source,
                adapter2.target,
                Coders.composeStateless(adapter1.coder, adapter2.coder));
    }

    /**
     * Compose two stateless adapters constructed from their source types, in turn composing their coders.
     */
    public static <T1, T2, T3, V1, V2, V3> Function<T1, Flow<Unit, StatelessAdapter<T1, T3, V1, V3>>> composeStateless(
            Function<T1, Flow<Unit, StatelessAdapter<T1, T2, V1, V2>>> constructor1,
            Function<T2, Flow<Unit, StatelessAdapter<T2, T3, V2, V3>>> constructor2) {
        return t1 -> Flows.bind(
                constructor1.apply(t1),
                firstMile -> Flows.map(
                        constructor2.apply(firstMile.target),
                        lastMile -> composeStateless(firstMile, lastMile)));
    }
}
