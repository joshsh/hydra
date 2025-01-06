package hydra;

import hydra.compute.Coder;
import hydra.compute.Flow;
import hydra.compute.StatelessCoder;
import hydra.core.Unit;
import hydra.dsl.Flows;


/**
 * Convenience functions for working with Hydra coders.
 */
public class Coders {
    /**
     * Compose two coders, chaining their encode and decode functions.
     */
    public static <S1, S2, V1, V2, V3> Coder<S1, S2, V1, V3> compose(
            Coder<S1, S2, V1, V2> coder1,
            Coder<S1, S2, V2, V3> coder2) {
        return new Coder<S1, S2, V1, V3>(
                Flows.compose(coder1.encode, coder2.encode),
                Flows.compose(coder2.decode, coder1.decode));
    }

    /**
     * Compose two stateless coders, chaining their encode and decode functions.
     */
    public static <V1, V2, V3> StatelessCoder<V1, V3> composeStateless(
            Coder<Unit, Unit, V1, V2> coder1,
            Coder<Unit, Unit, V2, V3> coder2) {
        return new StatelessCoder<>(
                Flows.compose(coder1.encode, coder2.encode),
                Flows.compose(coder2.decode, coder1.decode));
    }

    /**
     * Find the inverse of a coder.
     */
    public static <S1, S2, V1, V2> Coder<S2, S1, V2, V1> inverse(Coder<S1, S2, V1, V2> coder) {
        return new Coder<>(coder.decode, coder.encode);
    }

    /**
     * Find the inverse of a stateless coder.
     */
    public static <V1, V2> StatelessCoder<V2, V1> inverseStateless(Coder<Unit, Unit, V1, V2> coder) {
        return new StatelessCoder<V2, V1>(coder.decode, coder.encode);
    }

    /**
     * Pass an initial value through the Coder's encode function, then back through the decode function.
     */
    public static <S, V1, V2> Flow<S, V1> roundTrip(Coder<S, S, V1, V2> coder, V1 initialValue) {
        return Flows.compose(coder.encode, coder.decode).apply(initialValue);
    }
}
