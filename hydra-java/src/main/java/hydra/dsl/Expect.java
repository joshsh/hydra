package hydra.dsl;

import hydra.Reduction;
import hydra.compute.Flow;
import hydra.core.Field;
import hydra.core.FloatValue;
import hydra.core.IntegerValue;
import hydra.core.Literal;
import hydra.core.Name;
import hydra.core.Term;
import hydra.core.Type;
import hydra.graph.Graph;
import hydra.tools.PrettyPrinter;
import hydra.util.Opt;
import hydra.util.Tuple;
import java.math.BigInteger;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static hydra.dsl.Flows.bind;
import static hydra.dsl.Flows.fail;
import static hydra.dsl.Flows.mapM;
import static hydra.dsl.Flows.pure;
import static hydra.dsl.Flows.unexpected;


/**
 * Functions for decoding of native Java values from Hydra terms.
 */
public class Expect {
    private Expect() {
    }

    /**
     * Decode a bigfloat value.
     */
    public static <S> Flow<S, Double> bigfloat(final Term term) {
        return bind(float_(term), floatValue -> floatValue.accept(new FloatValue.PartialVisitor<Flow<S, Double>>() {
            @Override
            public Flow<S, Double> otherwise(FloatValue instance) {
                return wrongType("bigfloat", term);
            }

            @Override
            public Flow<S, Double> visit(FloatValue.Bigfloat instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Decode a bigint value.
     */
    public static <S> Flow<S, BigInteger> bigint(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, BigInteger>>() {
                    @Override
                    public Flow<S, BigInteger> otherwise(IntegerValue instance) {
                        return wrongType("bigint", term);
                    }

                    @Override
                    public Flow<S, BigInteger> visit(IntegerValue.Bigint instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode a binary value.
     */
    public static <S> Flow<S, String> binary(final Term term) {
        return bind(literal(term), literal -> literal.accept(new Literal.PartialVisitor<Flow<S, String>>() {
            @Override
            public Flow<S, String> otherwise(Literal instance) {
                return wrongType("binary", term);
            }

            @Override
            public Flow<S, String> visit(Literal.Binary instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Decode a boolean value.
     */
    public static <S> Flow<S, Boolean> boolean_(final Term term) {
        return bind(literal(term), literal -> literal.accept(new Literal.PartialVisitor<Flow<S, Boolean>>() {
            @Override
            public Flow<S, Boolean> otherwise(Literal instance) {
                return wrongType("boolean", term);
            }

            @Override
            public Flow<S, Boolean> visit(Literal.Boolean_ instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Retrieve and decode a field from a map of field names to terms.
     */
    public static <S, X> Flow<S, X> field(final Name fname,
                                          final Function<Term, Flow<S, X>> accessor,
                                          final Map<Name, Term> fields) {
        Term term = fields.get(fname);
        if (term == null) {
            return Flows.fail("field " + fname + " not found");
        } else {
            return accessor.apply(term);
        }
    }

    /**
     * Decode a floating point value.
     */
    public static <S> Flow<S, FloatValue> float_(final Term term) {
        return bind(literal(term), literal -> literal.accept(new Literal.PartialVisitor<Flow<S, FloatValue>>() {
            @Override
            public Flow<S, FloatValue> otherwise(Literal instance) {
                return wrongType("float", term);
            }

            @Override
            public Flow<S, FloatValue> visit(Literal.Float_ instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Decode a float32 value.
     */
    public static <S> Flow<S, Float> float32(final Term term) {
        return bind(float_(term), floatValue -> floatValue.accept(new FloatValue.PartialVisitor<Flow<S, Float>>() {
            @Override
            public Flow<S, Float> otherwise(FloatValue instance) {
                return wrongType("float32", term);
            }

            @Override
            public Flow<S, Float> visit(FloatValue.Float32 instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Decode a float64 value.
     */
    public static <S> Flow<S, Double> float64(final Term term) {
        return bind(float_(term), floatValue -> floatValue.accept(new FloatValue.PartialVisitor<Flow<S, Double>>() {
            @Override
            public Flow<S, Double> otherwise(FloatValue instance) {
                return wrongType("float64", term);
            }

            @Override
            public Flow<S, Double> visit(FloatValue.Float64 instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Decode a function.
     */
    public static <X, Y> Function<X, Flow<Graph, Y>> function(
            final Function<X, Term> fin,
            final Function<Term, Flow<Graph, Y>> fout,
            final Term func) {
        return x -> bind(Reduction.reduce(false, Terms.apply(func, fin.apply(x))), fout);
    }

    /**
     * Decode an int8 value.
     */
    public static <S> Flow<S, Byte> int8(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, Byte>>() {
                    @Override
                    public Flow<S, Byte> otherwise(IntegerValue instance) {
                        return wrongType("int8", term);
                    }

                    @Override
                    public Flow<S, Byte> visit(IntegerValue.Int8 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode an int16 value.
     */
    public static <S> Flow<S, Short> int16(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, Short>>() {
                    @Override
                    public Flow<S, Short> otherwise(IntegerValue instance) {
                        return wrongType("int16", term);
                    }

                    @Override
                    public Flow<S, Short> visit(IntegerValue.Int16 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode an int32 value.
     */
    public static <S> Flow<S, Integer> int32(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, Integer>>() {
                    @Override
                    public Flow<S, Integer> otherwise(IntegerValue instance) {
                        return wrongType("int32", term);
                    }

                    @Override
                    public Flow<S, Integer> visit(IntegerValue.Int32 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode an int64 value.
     */
    public static <S> Flow<S, Long> int64(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, Long>>() {
                    @Override
                    public Flow<S, Long> otherwise(IntegerValue instance) {
                        return wrongType("int64", term);
                    }

                    @Override
                    public Flow<S, Long> visit(IntegerValue.Int64 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode an integer value.
     */
    public static <S> Flow<S, IntegerValue> integer(final Term term) {
        return bind(literal(term), literal -> literal.accept(new Literal.PartialVisitor<Flow<S, IntegerValue>>() {
            @Override
            public Flow<S, IntegerValue> otherwise(Literal instance) {
                return wrongType("float", term);
            }

            @Override
            public Flow<S, IntegerValue> visit(Literal.Integer_ instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Decode a list of values.
     */
    public static <S, X> Flow<S, List<X>> list(final Function<Term, Flow<S, X>> elems, final Term term) {
        return term.accept(new Term.PartialVisitor<Flow<S, List<X>>>() {
            @Override
            public Flow<S, List<X>> otherwise(Term instance) {
                return wrongType("list", term);
            }

            @Override
            public Flow<S, List<X>> visit(Term.List instance) {
                return mapM(instance.value, elems);
            }
        });
    }

    /**
     * Decode a literal value.
     */
    public static <S> Flow<S, Literal> literal(final Term term) {
        return term.accept(new Term.PartialVisitor<Flow<S, Literal>>() {
            @Override
            public Flow<S, Literal> otherwise(Term instance) {
                return wrongType("literal", term);
            }

            @Override
            public Flow<S, Literal> visit(Term.Literal instance) {
                return pure(instance.value);
            }
        });
    }

    /**
     * Decode a map of keys to values.
     */
    public static <S, K, V> Flow<S, Map<K, V>> map(
            final Function<Term, Flow<S, K>> keys,
            final Function<Term, Flow<S, V>> values,
            final Term term) {
        return term.accept(new Term.PartialVisitor<Flow<S, Map<K, V>>>() {
            @Override
            public Flow<S, Map<K, V>> otherwise(Term instance) {
                return wrongType("map", term);
            }

            @Override
            public Flow<S, Map<K, V>> visit(Term.Map instance) {
                return Flows.map(Flows.mapM(new ArrayList<>(instance.value.entrySet()),
                                entry -> Flows.map2(
                                        keys.apply(entry.getKey()),
                                        values.apply(entry.getValue()),
                                        AbstractMap.SimpleEntry::new)),
                        (Function<List<Map.Entry<K, V>>, Map<K, V>>) entries -> {
                            Map<K, V> result = new HashMap<>();
                            for (Map.Entry<K, V> e : entries) {
                                result.put(e.getKey(), e.getValue());
                            }
                            return result;
                        });
            }
        });
    }

    /**
     * Decode an optional value.
     */
    public static <S, X> Flow<S, Opt<X>> optional(final Function<Term, Flow<S, X>> elems,
                                                  final Term term) {
        return term.accept(new Term.PartialVisitor<Flow<S, Opt<X>>>() {
            @Override
            public Flow<S, Opt<X>> otherwise(Term instance) {
                return wrongType("optional", term);
            }

            @Override
            public Flow<S, Opt<X>> visit(Term.Optional instance) {
                return instance.value.isPresent() ? Flows.map(elems.apply(instance.value.get()), Opt::of)
                        : pure(Opt.empty());
            }
        });
    }

    /**
     * Decode a pair of values.
     */
    public static <S, T1, T2> Flow<S, Tuple.Tuple2<T1, T2>> pair(
            final Function<Term, Flow<S, T1>> first,
            final Function<Term, Flow<S, T2>> second,
            final Term term) {
        return term.accept(new Term.PartialVisitor<Flow<S, Tuple.Tuple2<T1, T2>>>() {
            @Override
            public Flow<S, Tuple.Tuple2<T1, T2>> otherwise(Term instance) {
                return wrongType("tuple", term);
            }

            @Override
            public Flow<S, Tuple.Tuple2<T1, T2>> visit(Term.Product instance) {
                List<Term> values = instance.value;
                if (values.size() != 2) {
                    return fail("Expected a tuple of size 2, but found " + values.size());
                }
                return Flows.map2(first.apply(values.get(0)), second.apply(values.get(1)), Tuple.Tuple2::new);
            }
        });
    }

    /**
     * Decode a record.
     */
    public static <S> Flow<S, List<Field>> record(final Name tname, final Term term) {
        return term.accept(new Term.PartialVisitor<Flow<S, List<Field>>>() {
            @Override
            public Flow<S, List<Field>> otherwise(Term instance) {
                return wrongType("record", term);
            }

            @Override
            public Flow<S, List<Field>> visit(Term.Record instance) {
                if (instance.value.typeName.equals(tname)) {
                    return pure(instance.value.fields);
                } else {
                    return fail("Expected a record of type " + tname + ", but found " + instance.value.typeName);
                }
            }
        });
    }

    /**
     * Decode a record as a map from field names to terms.
     */
    public static <S> Flow<S, Map<Name, Term>> recordAsMap(final Name tname, final Term term) {
        return Flows.map(record(tname, term), fields -> {
            Map<Name, Term> result = new HashMap<>();
            for (Field f : fields) {
                result.put(f.name, f.term);
            }
            return result;
        });
    }

    /**
     * Decode a set of values.
     */
    public static <S, X> Flow<S, Set<X>> set(final Function<Term, Flow<S, X>> elems, final Term term) {
        return term.accept(new Term.PartialVisitor<Flow<S, Set<X>>>() {
            @Override
            public Flow<S, Set<X>> otherwise(Term instance) {
                return wrongType("set", term);
            }

            @Override
            public Flow<S, Set<X>> visit(Term.Set instance) {
                return mapM(instance.value, elems);
            }
        });
    }

    /**
     * Decode a string value.
     */
    public static <S> Flow<S, String> string(final Term term) {
        return bind(literal(term), literal -> literal.accept(new Literal.PartialVisitor<Flow<S, String>>() {
            @Override
            public Flow<S, String> otherwise(Literal instance) {
                return wrongType("string", term);
            }

            @Override
            public Flow<S, String> visit(Literal.String_ instance) {
                return pure(instance.value);
            }
        }));
    }

    /**
     * Decode a term.
     */
    public static <S> Flow<S, Term> term(final Term term) {
        return pure(term);
    }

    /**
     * Decode a type.
     */
    public static <S> Flow<S, Type> type(final Term term) {
        return fail("Core decoding not yet implemented");
    }

    /**
     * Decode a uint8 value.
     */
    public static <S> Flow<S, Character> uint8(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, Character>>() {
                    @Override
                    public Flow<S, Character> otherwise(IntegerValue instance) {
                        return wrongType("uint8", term);
                    }

                    @Override
                    public Flow<S, Character> visit(IntegerValue.Uint8 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode a uint16 value.
     */
    public static <S> Flow<S, Character> uint16(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, Character>>() {
                    @Override
                    public Flow<S, Character> otherwise(IntegerValue instance) {
                        return wrongType("uint16", term);
                    }

                    @Override
                    public Flow<S, Character> visit(IntegerValue.Uint16 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode a uint32 value.
     */
    public static <S> Flow<S, Long> uint32(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, Long>>() {
                    @Override
                    public Flow<S, Long> otherwise(IntegerValue instance) {
                        return wrongType("uint32", term);
                    }

                    @Override
                    public Flow<S, Long> visit(IntegerValue.Uint32 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    /**
     * Decode a uint64 value.
     */
    public static <S> Flow<S, BigInteger> uint64(final Term term) {
        return bind(integer(term),
                integerValue -> integerValue.accept(new IntegerValue.PartialVisitor<Flow<S, BigInteger>>() {
                    @Override
                    public Flow<S, BigInteger> otherwise(IntegerValue instance) {
                        return wrongType("uint64", term);
                    }

                    @Override
                    public Flow<S, BigInteger> visit(IntegerValue.Uint64 instance) {
                        return pure(instance.value);
                    }
                }));
    }

    private static <S, X> Flow<S, X> wrongType(String category, Term term) {
        return unexpected(category, PrettyPrinter.printTerm(term));
    }
}
