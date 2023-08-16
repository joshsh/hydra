package hydra.lib.equality;

import hydra.lib.PrimitiveType;

import java.util.function.Function;


public class EqualBoolean<A> extends EqualityFunction<A, Boolean> {
    public EqualBoolean() {
        super(PrimitiveType.boolean_());
    }

    public static Function<Boolean, Boolean> apply(Boolean second) {
        return first -> apply(first, second);
    }

    public static Boolean apply(Boolean first, Boolean second) {
        return 0 == first.compareTo(second);
    }
}
