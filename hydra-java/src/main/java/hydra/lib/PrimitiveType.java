package hydra.lib;

import hydra.compute.Flow;
import hydra.core.Term;
import hydra.core.Type;
import hydra.dsl.Expect;
import hydra.dsl.Types;
import hydra.graph.Graph;

import java.math.BigInteger;
import java.util.Comparator;
import java.util.function.Function;

import static hydra.dsl.Types.variable;

/**
 * A wrapper for a type which can be used as the basis of equality and comparison primitives
 */
public class PrimitiveType<A, T> {
    public final String name;
    public final Type<A> type;
    public final Function<Term<A>, Flow<Graph<A>, T>> expect;
    public final Comparator<T> comparator;

    public PrimitiveType(String name,
                         Type<A> type,
                         Function<Term<A>, Flow<Graph<A>, T>> expect,
                         Comparator<T> comparator) {
        this.name = name;
        this.type = type;
        this.expect = expect;
        this.comparator = comparator;
    }

    public static <A> PrimitiveType<A, Boolean> boolean_() {
        return new PrimitiveType<A, Boolean>("boolean", Types.boolean_(), Expect::boolean_, Boolean::compareTo);
    }

    public static <A> PrimitiveType<A, Double> bigfloat() {
        return new PrimitiveType<A, Double>("bigfloat", Types.bigfloat(), Expect::bigfloat, Double::compareTo);
    }

    public static <A> PrimitiveType<A, BigInteger> bigint() {
        return new PrimitiveType<A, BigInteger>("bigint", Types.bigint(), Expect::bigint, BigInteger::compareTo);
    }

    public static <A> PrimitiveType<A, String> binary() {
        return new PrimitiveType<A, String>("binary", Types.binary(), Expect::binary, String::compareTo);
    }

    public static <A> PrimitiveType<A, Float> float32() {
        return new PrimitiveType<A, Float>("float32", Types.float32(), Expect::float32, Float::compareTo);
    }

    public static <A> PrimitiveType<A, Double> float64() {
        return new PrimitiveType<A, Double>("float64", Types.float64(), Expect::float64, Double::compareTo);
    }

    public static <A> PrimitiveType<A, Short> int8() {
        return new PrimitiveType<A, Short>("int8", Types.int8(), Expect::int8, Short::compareTo);
    }

    public static <A> PrimitiveType<A, Short> int16() {
        return new PrimitiveType<A, Short>("int16", Types.int16(), Expect::int16, Short::compareTo);
    }

    public static <A> PrimitiveType<A, Integer> int32() {
        return new PrimitiveType<A, Integer>("int32", Types.int32(), Expect::int32, Integer::compareTo);
    }

    public static <A> PrimitiveType<A, Long> int64() {
        return new PrimitiveType<A, Long>("int64", Types.int64(), Expect::int64, Long::compareTo);
    }

    public static <A> PrimitiveType<A, String> string() {
        return new PrimitiveType<A, String>("string", Types.string(), Expect::string, String::compareTo);
    }

    public static <A> PrimitiveType<A, Term<A>> term() {
        return new PrimitiveType<A, Term<A>>(
                "term",
                hydra.dsl.Types.apply(variable(Term.NAME), variable("a")),
                Expect::term,
                (a, b) -> {throw new UnsupportedOperationException("Term comparison is not yet supported");});
    }

    public static <A> PrimitiveType<A, Type<A>> type() {
        return new PrimitiveType<A, Type<A>>(
                "type",
                hydra.dsl.Types.apply(variable(Type.NAME), variable("a")),
                Expect::type,
                (a, b) -> {throw new UnsupportedOperationException("Type comparison is not yet supported");});
    }

    public static <A> PrimitiveType<A, Byte> uint8() {
        return new PrimitiveType<A, Byte>("uint8", Types.uint8(), Expect::uint8, Byte::compareTo);
    }

    public static <A> PrimitiveType<A, Character> uint16() {
        return new PrimitiveType<A, Character>("uint16", Types.uint16(), Expect::uint16, Character::compareTo);
    }

    public static <A> PrimitiveType<A, Long> uint32() {
        return new PrimitiveType<A, Long>("uint32", Types.uint32(), Expect::uint32, Long::compareTo);
    }

    public static <A> PrimitiveType<A, BigInteger> uint64() {
        return new PrimitiveType<A, BigInteger>("uint64", Types.uint64(), Expect::uint64, BigInteger::compareTo);
    }
}
