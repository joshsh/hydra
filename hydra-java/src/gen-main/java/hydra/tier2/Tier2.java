// Note: this is an automatically generated file. Do not edit.

package hydra.tier2;

import hydra.dsl.Flows;


/**
 * A module for miscellaneous tier-2 functions and constants.
 */
public interface Tier2 {
  static <S> hydra.compute.Flow<S, S> getState() {
    return new hydra.compute.Flow((java.util.function.Function<java.lang.Void, java.util.function.Function<hydra.compute.Trace, hydra.compute.FlowState>>) (s0 -> (java.util.function.Function<hydra.compute.Trace, hydra.compute.FlowState>) (t0 -> {
      hydra.compute.Flow<Void, S> f1 = Flows.pure(null);
      hydra.compute.FlowState<Void, S> fs1 = f1.value.apply(s0).apply(t0);
      return ((((fs1)).value).map((ignored -> new hydra.compute.FlowState(hydra.util.Opt.of(((fs1)).state), ((fs1)).state, ((fs1)).trace)))).orElse(new hydra.compute.FlowState(hydra.util.Opt.empty(), ((fs1)).state, ((fs1)).trace));
    })));
  }

  static hydra.util.Opt<hydra.core.Type> getTermType(hydra.core.Term v1) {
    return ((v1)).accept(new hydra.core.Term.PartialVisitor<>() {
      @Override
      public hydra.util.Opt<hydra.core.Type> otherwise(hydra.core.Term instance) {
        return hydra.util.Opt.empty();
      }

      @Override
      public hydra.util.Opt<hydra.core.Type> visit(hydra.core.Term.Annotated instance) {
        return hydra.tier2.Tier2.getTermType(((instance.value)).subject);
      }

      @Override
      public hydra.util.Opt<hydra.core.Type> visit(hydra.core.Term.Typed instance) {
        return hydra.util.Opt.of(((instance.value)).type);
      }
    });
  }

  static <S> hydra.compute.Flow<S, java.lang.Void> putState(S cx) {
    return new hydra.compute.Flow<S, Void>((s0 -> (t0 -> {
      hydra.compute.Flow<S, Void> ff = Flows.pure(null);
      hydra.compute.FlowState<S, Void> f1 = ((ff.value).apply((s0))).apply((t0));
      return new hydra.compute.FlowState<>(f1.value, cx, f1.trace);
    })));
  }

  static <S, X> java.util.function.Function<String, hydra.compute.Flow<S, X>> unexpected(String expected) {
    return (java.util.function.Function<String, hydra.compute.Flow<S, X>>) (actual -> hydra.lib.flows.Fail.apply(hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
      hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
        hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "expected ",
          (expected))),
        " but found: ")),
      (actual)))));
  }
}