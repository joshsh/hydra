package hydra;

import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.compute.Trace;
import hydra.core.Unit;
import hydra.tier1.Tier1;
import hydra.tools.FlowException;
import hydra.tools.Function3;
import hydra.tools.Function4;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;


/**
 * A collection of convenience methods for constructing and composing flows, or stateful computations.
 */
public interface Flows {
    Trace EMPTY_TRACE
            = new Trace(Collections.emptyList(), Collections.emptyList(), Collections.emptyMap());

    /**
     * Apply a function flow to a domain value flow.
     */
    static <S, A, B> Flow<S, B> apply(Flow<S, Function<A, B>> mapping, Flow<S, A> input) {
        return new Flow<>(s0 -> t0 -> {
            FlowState<S, Function<A, B>> fs1 = mapping.value.apply(s0).apply(t0);
            Optional<Function<A, B>> mf = fs1.value;
            return mf.isPresent()
                    ? map(mf.get(), input).value.apply(fs1.state).apply(fs1.trace)
                    : new FlowState<>(Optional.empty(), fs1.state, fs1.trace);
        });
    }

    /**
     * Monadic bind function for flows.
     */
    static <S, A, B> Flow<S, B> bind(Flow<S, A> p, Function<A, Flow<S, B>> f) {
        return new Flow<>(s0 -> t0 -> {
            FlowState<S, A> fs1 = p.value.apply(s0).apply(t0);
            Optional<A> a = fs1.value;
            return a.isPresent()
                    ? f.apply(a.get()).value.apply(fs1.state).apply(fs1.trace)
                    : new FlowState<>(Optional.empty(), fs1.state, fs1.trace);
        });
    }

    /**
     * Monadic bind with reversed arguments.
     */
    static <S, A, B> Flow<S, B> bind(Function<A, Flow<S, B>> f, Flow<S, A> p) {
        return bind(f, p);
    }

    /**
     * Variant of monadic bind which takes two monadic arguments and a binary function.
     */
    static <S, A, B, C> Flow<S, C> bind2(Flow<S, A> p1, Flow<S, B> p2, BiFunction<A, B, Flow<S, C>> f) {
        return Flows.bind(p1, a -> Flows.bind(p2, b -> f.apply(a, b)));
    }

    /**
     * Two-argument monadic bind with reversed arguments.
     */
    static <S, A, B, C> Flow<S, C> bind2(BiFunction<A, B, Flow<S, C>> f, Flow<S, A> p1, Flow<S, B> p2) {
        return Flows.bind2(p1, p2, f);
    }

    /**
     * Variant of monadic bind which takes three monadic arguments and an arity-3 function.
     */
    static <S, A, B, C, D> Flow<S, D> bind3(Flow<S, A> p1,
                                            Flow<S, B> p2,
                                            Flow<S, C> p3,
                                            Function3<A, B, C, Flow<S, D>> f) {
        return Flows.bind(p1, a -> Flows.bind2(p2, p3, (b, c) -> f.apply(a, b, c)));
    }

    /**
     * Three-argument monadic bind with reversed arguments.
     */
    static <S, A, B, C, D> Flow<S, D> bind3(Function3<A, B, C, Flow<S, D>> f,
                                            Flow<S, A> p1,
                                            Flow<S, B> p2,
                                            Flow<S, C> p3) {
        return Flows.bind3(p1, p2, p3, f);
    }

    /**
     * Check whether a given value satisfies a list of predicates, returning the value itself if all checks are
     * successful, or a failure flow for the first predicate that fails.
     */
    static <S, A> Flow<S, A> check(A input, Function<A, Optional<String>>... predicates) {
        for (Function<A, Optional<String>> predicate : predicates) {
            Optional<String> msg = predicate.apply(input);
            if (msg.isPresent()) {
                return Flows.fail(msg.get());
            }
        }

        return pure(input);
    }

    /**
     * Compose two monadic functions, feeding the output of the first into the second.
     */
    static <S, A, B, C> Function<A, Flow<S, C>> compose(Function<A, Flow<S, B>> f, Function<B, Flow<S, C>> g) {
        return a -> Flows.bind(f.apply(a), g);
    }

    /**
     * Evaluate a flow and consume the result.
     */
    static <S, A> Flow<S, Unit> consume(Flow<S, A> x, Consumer<A> consumer) {
        return map(x, a -> {
            consumer.accept(a);
            return new Unit();
        });
    }

    /**
     * Produce a failure flow with the provided message.
     */
    static <S, A> Flow<S, A> fail(String msg) {
        return new Flow<>(s -> trace -> {
            String errMsg = "Error: " + msg; // TODO: include stack trace
            List<String> messages = new ArrayList<>(trace.messages);
            messages.add(errMsg);
            return new FlowState<>(Optional.empty(), s, trace.withMessages(messages));
        });
    }

    /**
     * Produce a failure flow with the provided message and additional information from a Throwable.
     */
    static <S, A> Flow<S, A> fail(String msg, Throwable cause) {
        return fail(msg + ": " + cause.getMessage());
    }

    /**
     * Extract the value from a flow, returning a default value instead if the flow failed.
     */
    static <S, A> A fromFlow(A dflt, S state, Flow<S, A> flow) {
        Function<S, Function<Flow<S, A>, A>> helper = Tier1.fromFlow(dflt);
        return helper.apply(state).apply(flow);
    }

    /**
     * Extract the value from a flow, throwing an exception if the flow failed.
     */
    static <S, A> A fromFlow(S state, Flow<S, A> flow) throws FlowException {
        FlowState<S, A> result = flow.value.apply(state).apply(EMPTY_TRACE);
        if (result.value.isPresent()) {
            return result.value.get();
        } else {
            throw new FlowException(result.trace);
        }
    }

    /**
     * Extract the value from a stateless flow, throwing an exception if the flow failed.
     */
    static <A> A fromFlow(Flow<Unit, A> flow) throws FlowException {
        return fromFlow(new Unit(), flow);
    }

    /**
     * Extract the state from a flow.
     */
    static <S> Flow<S, S> getState() {
        return new Flow<>(s0 -> t0 -> new FlowState<>(Optional.of(s0), s0, t0));
    }

    /**
     * Map a function over a flow.
     */
    static <S, A, B> Flow<S, B> map(Function<A, B> f, Flow<S, A> x) {
        return new Flow<>(s -> trace -> {
            FlowState<S, A> result = x.value.apply(s).apply(trace);
            return new FlowState<>(result.value.map(f), result.state, result.trace);
        });
    }

    /**
     * Map a function over a flow, with reversed arguments.
     */
    static <S, A, B> Flow<S, B> map(Flow<S, A> x, Function<A, B> f) {
        return map(f, x);
    }

    /**
     * Map a monadic function over a list, producing a flow of lists.
     */
    static <S, A, B> Flow<S, List<B>> mapM(List<A> as, Function<A, Flow<S, B>> f) {
        Flow<S, List<B>> result = pure(new ArrayList<>());
        for (A a : as) {
            result = bind(result, ys -> map(f.apply(a), b -> {
                ys.add(b); // Modify in place
                return ys;
            }));
        }
        return result;
    }

    /**
     * Map a monadic function over an array, producing a flow of lists.
     */
    static <S, A, B> Flow<S, List<B>> mapM(A[] xs, Function<A, Flow<S, B>> f) {
        return mapM(Arrays.asList(xs), f);
    }

    /**
     * Map a monadic function over the keys of a map, and another monadic function over the values of a map,
     * producing a flow of maps.
     */
    static <S, K1, V1, K2, V2> Flow<S, Map<K2, V2>> mapM(Map<K1, V1> xs,
                                                         Function<K1, Flow<S, K2>> kf,
                                                         Function<V1, Flow<S, V2>> vf) {
        Set<Map.Entry<K1, V1>> entries1 = xs.entrySet();
        Flow<S, Set<Map.Entry<K2, V2>>> entries2 = mapM(entries1,
                e -> bind(kf.apply(e.getKey()), k2 -> map(vf.apply(e.getValue()),
                        v2 -> new AbstractMap.SimpleEntry<>(k2, v2))));
        return map(entries2, entries -> entries.stream()
                .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
    }

    /**
     * Map a monadic function over an optional value, producing a flow of optionals.
     */
    static <S, A, B> Flow<S, Optional<B>> mapM(Optional<A> xs, Function<A, Flow<S, B>> f) {
        return xs.map(a -> map(f.apply(a), Optional::of)).orElseGet(() -> pure(Optional.empty()));
    }

    /**
     * Map a monadic function over a set, producing a flow of sets.
     */
    static <S, A, B> Flow<S, Set<B>> mapM(Set<A> as, Function<A, Flow<S, B>> f) {
        Flow<S, Set<B>> result = pure(new HashSet<>(as.size()));
        for (A a : as) {
            result = bind(result, ys -> map(f.apply(a), b -> {
                ys.add(b); // Modify in place
                return ys;
            }));
        }
        return result;
    }

    /**
     * Map a bifunction over two flows, producing a flow.
     */
    static <S, A, B, C> Flow<S, C> map2(Flow<S, A> x, Flow<S, B> y, BiFunction<A, B, C> f) {
        return Flows.bind(x, a1 -> Flows.bind(y, b1 -> Flows.pure(f.apply(a1, b1))));
    }

    /**
     * Map an arity-3 function over three flows, producing a flow.
     */
    static <S, A, B, C, D> Flow<S, D> map3(Flow<S, A> a, Flow<S, B> b, Flow<S, C> c, Function3<A, B, C, D> f) {
        return Flows.bind(a,
                a1 -> Flows.bind(b,
                        b1 -> Flows.bind(c,
                                c1 -> Flows.pure(f.apply(a1, b1, c1)))));
    }

    /**
     * Map an arity-4 function over four flows, producing a flow.
     */
    static <S, A, B, C, D, E> Flow<S, E> map4(Flow<S, A> a,
                                              Flow<S, B> b,
                                              Flow<S, C> c,
                                              Flow<S, D> d,
                                              Function4<A, B, C, D, E> f) {
        return Flows.bind(a,
                a1 -> Flows.bind(b,
                        b1 -> Flows.bind(c,
                                c1 -> Flows.bind(d,
                                        d1 -> Flows.pure(f.apply(a1, b1, c1, d1))))));
    }

    /**
     * Produce a given object as a pure flow; the value is guaranteed to be present,
     * and neither state nor trace are modified.
     */
    static <S, A> Flow<S, A> pure(A obj) {
        return new Flow<>(s -> trace -> new FlowState<>(Optional.of(obj), s, trace));
    }

    /**
     * Modify the state of a flow.
     */
    static <S> Flow<S, Boolean> putState(S snew) {
        // Note: for lack of a unit value other than null,
        // we use use a boolean as the ignorable value output of putState()
        return new Flow<>(s0 -> t0 -> new FlowState<>(Optional.of(true), snew, t0));
    }

    /**
     * Test an optional value, producing a flow with the value if present, or an error flow if absent.
     */
    static <S, A> Flow<S, A> require(Optional<A> optValue, String category) {
        return optValue.isPresent()
                ? Flows.pure(optValue.get())
                : Flows.fail("require " + category + " is missing/null");
    }

    /**
     * Evaluate each flow from left to right, and produce a flow of the resulting list.
     * Analogous to the sequence function in Haskell.
     */
    static <S, A> Flow<S, List<A>> sequence(List<Flow<S, A>> elements) {
        Flow<S, List<A>> result = Flows.pure(new ArrayList<>(elements.size()));
        for (Flow<S, A> element : elements) {
            result = Flows.bind(result, xs -> Flows.map(element, x -> {
                xs.add(x); // Modify in place
                return xs;
            }));
        }
        return result;
    }

    /**
     * Produce an error flow indicating an unexpected value.
     * For example, if you expect a string but find an integer, use unexpected("string", myInt).
     */
    static <S, A> Flow<S, A> unexpected(String cat, Object obj) {
        return fail("expected " + cat + " but found: " + obj);
    }

    /**
     * Produce an error flow indicating an unexpected class of value.
     */
    static <S, A> Flow<S, A> unexpectedClass(String cat, Object obj) {
        return fail("expected " + cat + " but found an instance of " + obj.getClass().getName());
    }

    /**
     * Continue a flow after adding a warning message.
     */
    static <S, A> Flow<S, A> warn(String message, Flow<S, A> flow) {
        Function<Flow<S, A>, Flow<S, A>> f = Tier1.warn(message);
        return f.apply(flow);
    }
}
