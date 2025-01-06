package hydra.dsl;

import hydra.compute.Flow;
import hydra.core.Unit;
import hydra.tools.Function3;
import hydra.tools.Function4;
import hydra.util.Opt;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;


/**
 * A convenient wrapper for a stateless Flow, providing fluent-style methods.
 * @param <A> the result type of the Flow
 */
public class Pipe<A> {
  /**
   * The wrapped Flow of the pipe.
   */
  public final Flow<Unit, A> flow;

  /**
   * Construct a pipe which wraps the given Flow.
   */
  public Pipe(Flow<Unit, A> flow) {
    this.flow = flow;
  }

  /**
   * Construct a pure pipe for a given object.
   */
  public Pipe(A obj) {
    flow = Flows.pure(obj);
  }

  /**
   * Evaluate a pipe and consume the result.
   */
  public Pipe<Unit> consume(Consumer<A> consumer) {
    return consume(this, consumer);
  }

  /**
   * Extract the value from a pipe, throwing an exception if the pipe failed.
   */
  public A eval() {
    return eval(this);
  }

  /**
   * Extract the value from a pipe, returning a default value instead if the pipe failed.
   */
  public A eval(A dflt) {
    return eval(this, dflt);
  }

  /**
   * Monadic bind function for pipes.
   */
  public <B> Pipe<B> flatMap(Function<A, Pipe<B>> f) {
    return flatMap(this, f);
  }

  /**
   * Variant of monadic bind which takes two monadic arguments and a binary function.
   */
  public <B, C> Pipe<C> flatMap2(Pipe<B> other, BiFunction<A, B, Pipe<C>> f) {
    return flatMap2(this, other, f);
  }

  /**
   * Variant of monadic bind which takes three monadic arguments and an arity-3 function.
   */
  public <B, C, D> Pipe<D> flatMap3(
      Pipe<B> other,
      Pipe<C> other2,
      Function3<A, B, C, Pipe<D>> f) {
    return flatMap3(this, other, other2, f);
  }

  /**
   * Map a function over a pipe, producing another pipe.
   */
  public <B> Pipe<B> map(Function<A, B> f) {
    return map(this, f);
  }

  /**
   * Map a bifunction over two pipes, producing a pipe.
   */
  public <B, C> Pipe<C> map2(Pipe<B> other, BiFunction<A, B, C> f) {
    return map2(this, other, f);
  }

  /**
   * Map an arity-3 function over three pipes, producing a pipe.
   */
  public <B, C, D> Pipe<D> map3(Pipe<B> other, Pipe<C> other2, Function3<A, B, C, D> f) {
    return map3(this, other, other2, f);
  }

  /**
   * Map an arity-4 function over four pipes, producing a pipe.
   */
  public <B, C, D, E> Pipe<E> map4(
      Pipe<B> other,
      Pipe<C> other2,
      Pipe<D> other3,
      Function4<A, B, C, D, E> f) {
    return map4(this, other, other2, other3, f);
  }

  /**
   * Continue a pipe after adding a warning message.
   */
  public Pipe<A> warn(String message) {
    return warn(message, this);
  }

  /**
   * Check whether a given value satisfies a list of predicates, returning the value itself if all checks are
   * successful, or a failure pipe for the first predicate that fails.
   */
  public static <A> Pipe<A> check(A input, Function<A, Opt<String>>... predicates) {
    return new Pipe<>(Flows.check(input, predicates));
  }

  /**
   * Compose two monadic functions, feeding the output of the first into the second.
   */
  public static <A, B, C> Function<A, Pipe<C>> compose(Function<A, Pipe<B>> f, Function<B, Pipe<C>> g) {
    Function<A, Flow<Unit, C>> fg = Flows.compose(a -> f.apply(a).flow, b -> g.apply(b).flow);
    return a -> new Pipe<>(fg.apply(a));
  }

  /**
   * Evaluate a pipe and consume the result.
   */
  public static <A> Pipe<Unit> consume(Pipe<A> pipe, Consumer<A> consumer) {
    return new Pipe<>(Flows.consume(pipe.flow, consumer));
  }

  /**
   * Extract the value from a pipe, throwing an exception if the pipe failed.
   */
  public static <A> A eval(Pipe<A> pipe) {
    return Flows.fromFlow(new Unit(), pipe.flow);
  }

  /**
   * Extract the value from a pipe, returning a default value instead if the pipe failed.
   */
  public static <A> A eval(Pipe<A> pipe, A dflt) {
    return Flows.fromFlow(dflt, new Unit(), pipe.flow);
  }

  /**
   * Produce a failure pipe with the provided message.
   */
  public static <A> Pipe<A> fail(String msg) {
    return new Pipe<>(Flows.fail(msg));
  }

  /**
   * Produce a failure pipe with the provided message and additional information from a Throwable.
   */
  public static <A> Pipe<A> fail(String msg, Throwable cause) {
    return new Pipe<>(Flows.fail(msg, cause));
  }

  /**
   * Monadic bind function for pipes.
   */
  public static <A, B> Pipe<B> flatMap(Pipe<A> a, Function<A, Pipe<B>> f) {
    return new Pipe<>(Flows.bind(a.flow, x -> f.apply(x).flow));
  }

  /**
   * Variant of monadic bind which takes two monadic arguments and a binary function.
   */
  public static <A, B, C> Pipe<C> flatMap2(Pipe<A> pipeA, Pipe<B> pipeB, BiFunction<A, B, Pipe<C>> f) {
    return new Pipe<>(Flows.bind2(pipeA.flow, pipeB.flow, (a, b) -> f.apply(a, b).flow));
  }

  /**
   * Variant of monadic bind which takes three monadic arguments and an arity-3 function.
   */
  public static <A, B, C, D> Pipe<D> flatMap3(
      Pipe<A> pipeA,
      Pipe<B> pipeB,
      Pipe<C> pipeC,
      Function3<A, B, C, Pipe<D>> f) {
    return new Pipe<>(Flows.bind3(pipeA.flow, pipeB.flow, pipeC.flow, (a, b, c) -> f.apply(a, b, c).flow));
  }

  /**
   * Map a function over a pipe, producing another pipe.
   */
  public static <A, B> Pipe<B> map(Pipe<A> pipe, Function<A, B> f) {
    return new Pipe<>(Flows.map(pipe.flow, f));
  }

  /**
   * Map a bifunction over two pipes, producing a pipe.
   */
  public static <A, B, C> Pipe<C> map2(Pipe<A> pipeA, Pipe<B> pipeB, BiFunction<A, B, C> f) {
    return new Pipe<>(Flows.map2(pipeA.flow, pipeB.flow, f));
  }

  /**
   * Map an arity-3 function over three pipes, producing a pipe.
   */
  public static <A, B, C, D> Pipe<D> map3(Pipe<A> pipeA, Pipe<B> pipeB, Pipe<C> pipeC, Function3<A, B, C, D> f) {
    return new Pipe<>(Flows.map3(pipeA.flow, pipeB.flow, pipeC.flow, f));
  }

  /**
   * Map an arity-4 function over four pipes, producing a pipe.
   */
  public static <A, B, C, D, E> Pipe<E> map4(
      Pipe<A> pipeA,
      Pipe<B> pipeB,
      Pipe<C> pipeC,
      Pipe<D> pipeD,
      Function4<A, B, C, D, E> f) {
    return new Pipe<>(Flows.map4(pipeA.flow, pipeB.flow, pipeC.flow, pipeD.flow, f));
  }

  /**
   * Map a monadic function over a list, producing a pipe of lists.
   */
  public static <A, B> Pipe<List<B>> mapM(List<A> as, Function<A, Pipe<B>> f) {
    return new Pipe<>(Flows.mapM(as, a -> f.apply(a).flow));
  }

  /**
   * Map a monadic function over an array, producing a pipe of lists.
   */
  public static <A, B> Pipe<List<B>> mapM(A[] xs, Function<A, Pipe<B>> f) {
    return new Pipe<>(Flows.mapM(xs, a -> f.apply(a).flow));
  }

  /**
   * Map a monadic function over the keys of a map, and another monadic function over the values of a map,
   * producing a pipe of maps.
   */
  public static <K1, V1, K2, V2> Pipe<Map<K2, V2>> mapM(Map<K1, V1> xs,
      Function<K1, Pipe<K2>> kf,
      Function<V1, Pipe<V2>> vf) {
    return new Pipe<>(Flows.mapM(xs, x -> kf.apply(x).flow, x -> vf.apply(x).flow));
  }

  /**
   * Map a monadic function over an optional value, producing a pipe of optionals.
   */
  public static <A, B> Pipe<Opt<B>> mapM(Opt<A> xs, Function<A, Pipe<B>> f) {
    return new Pipe<>(Flows.mapM(xs, x -> f.apply(x).flow));
  }

  /**
   * Map a monadic function over a set, producing a pipe of sets.
   */
  public static <A, B> Pipe<Set<B>> mapM(Set<A> as, Function<A, Pipe<B>> f) {
    return new Pipe<>(Flows.mapM(as, x -> f.apply(x).flow));
  }

  /**
   * Produce a given object as a pure pipe; the value is guaranteed to be present,
   * and neither state nor trace are modified.
   */
  public static <A> Pipe<A> pure(A obj) {
    return new Pipe<>(Flows.pure(obj));
  }

  /**
   * Evaluate each pipe from left to right, and produce a pipe of the resulting list.
   * Analogous to the sequence function in Haskell.
   */
  public static <A> Pipe<List<A>> sequence(List<Pipe<A>> elements) {
    List<Flow<Unit, A>> flows = new ArrayList<>(elements.size());
    for (Pipe<A> p : elements) {
      flows.add(p.flow);
    }
    return new Pipe<>(Flows.sequence(flows));
  }

  /**
   * Produce an error pipe indicating an unexpected value.
   * For example, if you expect a string but find an integer, use unexpected("string", myInt).
   */
  public static <A> Pipe<A> unexpected(String cat, Object obj) {
    return new Pipe<>(Flows.unexpected(cat, obj));
  }

  /**
   * Produce an error pipe indicating an unexpected class of value.
   */
  public static <A> Pipe<A> unexpectedClass(String cat, Object obj) {
    return new Pipe<>(Flows.unexpectedClass(cat, obj));
  }

  /**
   * Continue a pipe after adding a warning message.
   */
  public static <A> Pipe<A> warn(String message, Pipe<A> pipe) {
    return new Pipe<>(Flows.warn(message, pipe.flow));
  }
}
