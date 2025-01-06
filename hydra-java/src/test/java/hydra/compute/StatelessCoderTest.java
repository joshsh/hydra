package hydra.compute;

import hydra.HydraTestBase;
import org.junit.jupiter.api.Test;

import static hydra.Coders.composeStateless;
import static hydra.Coders.inverseStateless;
import static hydra.dsl.Flows.fail;
import static hydra.dsl.Flows.pure;


/**
 * A collection of tests illustrating the use of stateless coders, for simplicity.
 * Stateful coders are no different except that they involve stateful flows.
 */
public class StatelessCoderTest extends HydraTestBase {
    private static final StatelessCoder<Integer, Integer> addOneCoder = new StatelessCoder<>(
            i -> pure(i + 1),
            i -> pure(i - 1)
    );

    private static final StatelessCoder<Integer, Integer> mod7Coder = new StatelessCoder<>(
            i -> pure(i % 7),
            i -> fail("modulus operation is not reversible")
    );

    private static final StatelessCoder<Integer, String> toStringCoder = new StatelessCoder<>(
            i -> pure(i.toString()),
            s -> {
                try {
                    return pure(Integer.parseInt(s));
                } catch (NumberFormatException e) {
                    return fail(e.getMessage());
                }
            });

    @Test
    public void checkBidirectionalCoder() {
        // 1 is encoded to 2
        assertSucceedsWith(2, addOneCoder.encode.apply(1));
        // 2 is decoded back to 1
        assertSucceedsWith(1, addOneCoder.decode.apply(2));

        // Round-trip from 1 to 2 and back to 1 is a no-op
        assertRoundTripIsNoop(addOneCoder, 1);
    }

    @Test
    public void checkOneWayCoder() {
        // Normally, every coder has at least a working encode function
        assertSucceedsWith(2, mod7Coder.encode.apply(9));

        // This coder has a decode function which always fails; it is not meant to be used for decoding
        assertFails(mod7Coder.decode.apply(2));
    }

    @Test
    public void checkPartialBidirectionalCoder() {
        // For all values, a round-trip "from the left" is a no-op
        assertRoundTripIsNoop(toStringCoder, 1);

        // For certain values, a round-trip "from the right" is also a no-op
        StatelessCoder<String, Integer> inverse = inverseStateless(toStringCoder);
        assertRoundTripIsNoop(inverse, "42");

        // However, for some values, a round-trip "from the right" fails.
        // In this case, the value "not a number" cannot be decoded to an integer
        assertRoundTripFails(inverse, "not a number");
    }

    @Test
    public void checkInverses() {
        // The inverse of the "add one" coder is a "subtract one" coder;
        // it just swaps the encode and decode functions.
        StatelessCoder<Integer, Integer> subtractOneCoder = inverseStateless(addOneCoder);
        assertSucceedsWith(0, subtractOneCoder.encode.apply(1));
        assertSucceedsWith(1, subtractOneCoder.decode.apply(0));
    }

    @Test
    public void checkComposition() {
        // Compose two coders to create a new coder
        StatelessCoder<Integer, String> composed = composeStateless(addOneCoder, toStringCoder);
        StatelessCoder<String, Integer> inverse = inverseStateless(composed);

        // The composed encode function adds one, then converts the number to a string
        assertSucceedsWith("2", composed.encode.apply(1));

        // The composed decode function converts the string to a number, then subtracts one
        assertSucceedsWith(41, inverse.encode.apply("42"));

        // All round-trips "from the left" are no-ops
        assertRoundTripIsNoop(composed, 1);

        // Some round-trips "from the right" are no-ops
        assertRoundTripIsNoop(inverse, "42");

        // Other round-trips "from the right" fail, for the same reason that round-trips through toStringCoder fail
        assertRoundTripFails(inverse, "not a number");
    }
}