package hydra;

import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.compute.Trace;
import hydra.tier1.Tier1;
import hydra.tools.FlowException;
import hydra.tools.TriFunction;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;


/**
 * A collection of convenience methods for constructing and composing flows, or stateful computations.
 */
public interface Flows {
    Trace EMPTY_TRACE
            = new Trace(Collections.emptyList(), Collections.emptyList(), Collections.emptyMap());

    static <S, X, Y> Flow<S, Y> apply(Flow<S, Function<X, Y>> mapping, Flow<S, X> input) {
        return new Flow<>(s0 -> t0 -> {
            FlowState<S, Function<X, Y>> fs1 = mapping.value.apply(s0).apply(t0);
            Optional<Function<X, Y>> mf = fs1.value;
            return mf.isPresent()
                    ? map(mf.get(), input).value.apply(fs1.state).apply(fs1.trace)
                    : new FlowState<>(Optional.empty(), fs1.state, fs1.trace);
        });
    }

    /**
     * Monadic bind function for flows
     */
    static <S, X, Y> Flow<S, Y> bind(Flow<S, X> p, Function<X, Flow<S, Y>> k) {
        return new Flow<>(s0 -> t0 -> {
            FlowState<S, X> fs1 = p.value.apply(s0).apply(t0);
            Optional<X> x = fs1.value;
            return x.isPresent()
                    ? k.apply(x.get()).value.apply(fs1.state).apply(fs1.trace)
                    : new FlowState<>(Optional.empty(), fs1.state, fs1.trace);
        });
    }

    /**
     * Monadic bind with reversed arguments
     */
    static <S, X, Y> Flow<S, Y> bind(Function<X, Flow<S, Y>> k, Flow<S, X> p) {
        return bind(k, p);
    }

    /**
     * Variant of monadic bind which takes two monadic arguments and a binary function
     */
    static <S, X, Y, Z> Flow<S, Z> bind2(Flow<S, X> p1, Flow<S, Y> p2, BiFunction<X, Y, Flow <S, Z>> k) {
        return Flows.bind(p1, x -> Flows.bind(p2, y -> k.apply(x, y)));
    }

    /**
     * Two-argument monadic bind with reversed arguments
     */
    static <S, X, Y, Z> Flow<S, Z> bind2(BiFunction<X, Y, Flow <S, Z>> k, Flow<S, X> p1, Flow<S, Y> p2) {
        return Flows.bind2(p1, p2, k);
    }

    /**
     * Compose two monadic functions, feeding the output of the first into the second
     */
    static <S, X, Y, Z> Function<X, Flow<S, Z>> compose(Function<X, Flow<S, Y>> f, Function<Y, Flow<S, Z>> g) {
        return x -> Flows.bind(f.apply(x), g);
    }

    /**
     * Produce a failure flow with the provided message
     */
    static <S, X> Flow<S, X> fail(String msg) {
        return new Flow<>(s -> trace -> {
            String errMsg = "Error: " + msg; // TODO: include stack trace
            List<String> messages = new ArrayList<>(trace.messages);
            messages.add(errMsg);
            return new FlowState<>(Optional.empty(), s, trace.withMessages(messages));
        });
    }

    /**
     * Extract the value from a flow, returning a default value instead if the flow failed.
     */
    static <S, X> X fromFlow(X dflt, S state, Flow<S, X> flow) {
        Function<S, Function<Flow<S, X>, X>> helper = Tier1.fromFlow(dflt);
        return helper.apply(state).apply(flow);
    }

    /**
     * Extract the state from a flow
     */
    static <S> Flow<S, S> getState() {
      return new Flow<>(s0 -> t0 -> new FlowState<>(Optional.of(s0), s0, t0));
    }

    /**
     * Map a function over a flow
     */
    static <S, X, Y> Flow<S, Y> map(Function<X, Y> f, Flow <S, X> x) {
        return new Flow<>(s -> trace -> {
            FlowState<S, X> result = x.value.apply(s).apply(trace);
            return new FlowState<>(result.value.map(f), result.state, result.trace);
        });
    }

    /**
     * Map a function over a flow, with reversed arguments
     */
    static <S, X, Y> Flow<S, Y> map(Flow <S, X> x, Function<X, Y> f) {
        return map(f, x);
    }

    /**
     * Map a monadic function over a list, producing a flow of lists
     */
    static <S, X, Y> Flow<S, List<Y>> mapM(List<X> xs, Function<X, Flow<S, Y>> f) {
        Flow<S, List<Y>> result = pure(new ArrayList<>());
        for (X x : xs) {
            result = bind(result, ys -> map(f.apply(x), y -> {
                ys.add(y); // Modify in place
                return ys;
            }));
        }
        return result;
    }

    /**
     * Map a monadic function over the keys of a map, and another monadic function over the values of a map,
     * producing a flow of maps
     */
    static <S, K1, V1, K2, V2> Flow<S, Map<K2, V2>> mapM(Map<K1, V1> xs, Function<K1, Flow<S, K2>> kf, Function<V1, Flow<S, V2>> vf) {
        Set<Map.Entry<K1, V1>> entries1 = xs.entrySet();
        Flow<S, Set<Map.Entry<K2, V2>>> entries2 = mapM(entries1,
                e -> bind(kf.apply(e.getKey()), k2 -> map(vf.apply(e.getValue()), v2 -> new AbstractMap.SimpleEntry<>(k2, v2))));
        return map(entries2, entries -> entries.stream().collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
    }

    /**
     * Map a monadic function over an optional value, producing a flow of optionals
     */
    static <S, X, Y> Flow<S, Optional<Y>> mapM(Optional<X> xs, Function<X, Flow<S, Y>> f) {
        return xs.map(x -> map(f.apply(x), Optional::of)).orElseGet(() -> pure(Optional.empty()));
    }

    /**
     * Map a monadic function over a set, producing a flow of sets
     */
    static <S, X, Y> Flow<S, Set<Y>> mapM(Set<X> xs, Function<X, Flow<S, Y>> f) {
        Flow<S, Set<Y>> result = pure(new HashSet<>(xs.size()));
        for (X x : xs) {
            result = bind(result, ys -> map(f.apply(x), y -> {
                ys.add(y); // Modify in place
                return ys;
            }));
        }
        return result;
    }

    /**
     * Map a bifunction over two flows, producing a flow
     */
    static <S, X, Y, Z> Flow<S, Z> map2(Flow<S, X> x, Flow<S, Y> y, BiFunction<X, Y, Z> f) {
        return Flows.bind(x, x1 -> Flows.bind(y, y1 -> Flows.pure(f.apply(x1, y1))));
    }

    /**
     * Map a ternary function over three flowr, producing a flow
     */
    static <S, X, Y, Z, R> Flow<S, R> map3(Flow<S, X> x, Flow<S, Y> y, Flow<S, Z> z, TriFunction<X, Y, Z, R> f) {
        return Flows.bind(x, x1 -> Flows.bind(y, y1 -> Flows.bind(z, z1 -> Flows.pure(f.apply(x1, y1, z1)))));
    }

    /**
     * Produce a given object as a pure flow; the value is guaranteed to be present, and neither state nor trace are modified
     */
    static <S, X> Flow<S, X> pure(X obj) {
        return new Flow<>(s -> trace -> new FlowState<>(Optional.of(obj), s, trace));
    }

    /**
     * Modify the state of a flow
     */
    static <S> Flow<S, Boolean> putState(S snew) {
        // Note: for lack of a unit value other than null, we use use a boolean as the ignorable value output of putState()
        return new Flow<>(s0 -> t0 -> new FlowState<>(Optional.of(true), snew, t0));
    }

    /**
     * Produce an error flow indicating an unexpected value.
     * For example, if you expect a string but find an integer, use unexpected("string", myInt)
     */
    static <S, X> Flow<S, X> unexpected(String cat, Object obj) {
        return fail("expected " + cat + " but found: " + obj);
    }

    /**
     * Continue a flow after adding a warning message
     */
    static <S, X> Flow<S, X> warn(String message, Flow<S, X> flow) {
        Function<Flow<S, X>, Flow<S, X>> f = Tier1.warn(message);
        return f.apply(flow);
    }
}
