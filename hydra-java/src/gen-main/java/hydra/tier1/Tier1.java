package hydra.tier1;

import hydra.compute.Flow;
import hydra.compute.FlowState;
import hydra.compute.Trace;
import hydra.mantle.Either;

import java.util.function.Function;

/**
 * A module for miscellaneous tier-1 functions and constants.
 */
public interface Tier1 {
  static Double floatValueToBigfloat(hydra.core.FloatValue v1) {
    return ((v1)).accept(new hydra.core.FloatValue.Visitor<Double>() {
      @Override
      public Double visit(hydra.core.FloatValue.Bigfloat instance) {
        return hydra.lib.equality.Identity.apply((instance.value));
      }
      
      @Override
      public Double visit(hydra.core.FloatValue.Float32 instance) {
        return hydra.lib.literals.Float32ToBigfloat.apply((instance.value));
      }
      
      @Override
      public Double visit(hydra.core.FloatValue.Float64 instance) {
        return hydra.lib.literals.Float64ToBigfloat.apply((instance.value));
      }
    });
  }
  
  static java.math.BigInteger integerValueToBigint(hydra.core.IntegerValue v1) {
    return ((v1)).accept(new hydra.core.IntegerValue.Visitor<java.math.BigInteger>() {
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Bigint instance) {
        return hydra.lib.equality.Identity.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Int8 instance) {
        return hydra.lib.literals.Int8ToBigint.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Int16 instance) {
        return hydra.lib.literals.Int16ToBigint.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Int32 instance) {
        return hydra.lib.literals.Int32ToBigint.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Int64 instance) {
        return hydra.lib.literals.Int64ToBigint.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Uint8 instance) {
        return hydra.lib.literals.Uint8ToBigint.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Uint16 instance) {
        return hydra.lib.literals.Uint16ToBigint.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Uint32 instance) {
        return hydra.lib.literals.Uint32ToBigint.apply((instance.value));
      }
      
      @Override
      public java.math.BigInteger visit(hydra.core.IntegerValue.Uint64 instance) {
        return hydra.lib.literals.Uint64ToBigint.apply((instance.value));
      }
    });
  }
  
  static <A> Boolean isLambda(hydra.core.Term<A> term) {
    return (hydra.strip.Strip.stripTerm((term))).accept(new hydra.core.Term.PartialVisitor<A, Boolean>() {
      @Override
      public Boolean otherwise(hydra.core.Term<A> instance) {
        return false;
      }
      
      @Override
      public Boolean visit(hydra.core.Term.Function<A> instance) {
        return ((instance.value)).accept(new hydra.core.Function.PartialVisitor<A, Boolean>() {
          @Override
          public Boolean otherwise(hydra.core.Function<A> instance) {
            return false;
          }
          
          @Override
          public Boolean visit(hydra.core.Function.Lambda<A> instance) {
            return true;
          }
        });
      }
      
      @Override
      public Boolean visit(hydra.core.Term.Let<A> instance) {
        return hydra.tier1.Tier1.isLambda(((instance.value)).environment);
      }
    });
  }
  
  static hydra.core.Name unqualifyName(hydra.module.QualifiedName qname) {
    String prefix = ((((qname)).namespace).map((java.util.function.Function<hydra.module.Namespace, String>) (n -> hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
      ((n)).value,
      "."))))).orElse("");
    return new hydra.core.Name(hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
      (prefix),
      ((qname)).local)));
  }
  
  hydra.compute.Trace emptyTrace = new hydra.compute.Trace(java.util.Arrays.asList(), java.util.Arrays.asList(), hydra.lib.maps.Empty.apply());
  
  static <A, S> java.util.function.Function<hydra.compute.Flow<S, A>, Boolean> flowSucceeds(S cx) {
    return (java.util.function.Function<hydra.compute.Flow<S, A>, Boolean>) (f -> hydra.lib.optionals.IsJust.apply((((((f)).value).apply((cx))).apply((hydra.tier1.Tier1.emptyTrace))).value));
  }
  
  static <A, S> java.util.function.Function<S, java.util.function.Function<hydra.compute.Flow<S, A>, A>> fromFlow(A def) {
    return (java.util.function.Function<S, java.util.function.Function<hydra.compute.Flow<S, A>, A>>) (cx -> (java.util.function.Function<hydra.compute.Flow<S, A>, A>) (f -> (((((((f)).value).apply((cx))).apply((hydra.tier1.Tier1.emptyTrace))).value).map((java.util.function.Function<A, A>) (x -> (x)))).orElse((def))));
  }
  
  static <A, S> java.util.function.Function<java.util.function.Function<hydra.compute.Trace, java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>>, java.util.function.Function<hydra.compute.Flow<S, A>, hydra.compute.Flow<S, A>>> mutateTrace(java.util.function.Function<hydra.compute.Trace, hydra.mantle.Either<String, hydra.compute.Trace>> mutate) {
    return (java.util.function.Function<java.util.function.Function<hydra.compute.Trace, java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>>, java.util.function.Function<hydra.compute.Flow<S, A>, hydra.compute.Flow<S, A>>>) (restore -> (java.util.function.Function<hydra.compute.Flow<S, A>, hydra.compute.Flow<S, A>>) (f -> new hydra.compute.Flow<S, A>((java.util.function.Function<S, java.util.function.Function<hydra.compute.Trace, hydra.compute.FlowState<S, A>>>) (s0 -> (java.util.function.Function<hydra.compute.Trace, hydra.compute.FlowState<S, A>>) (t0 -> {
      java.util.function.Function<hydra.compute.Trace, hydra.compute.FlowState<S, A>> forRight = t1 -> {
        hydra.compute.FlowState<S, A> f2 = ((((f)).value).apply((s0))).apply((t1));
        return new hydra.compute.FlowState<>(((f2)).value, ((f2)).state, (((restore)).apply((t0))).apply(((f2)).trace));
      };
      java.util.function.Function<String, hydra.compute.FlowState<S, A>> forLeft = msg -> new hydra.compute.FlowState<>(java.util.Optional.empty(), (s0), (Tier1.pushError((msg))).apply((t0)));
      return mutate.apply(t0).accept(new Either.Visitor<String, Trace, FlowState<S, A>>() {
        @Override
        public FlowState<S, A> visit(Either.Left<String, Trace> instance) {
          return ((forLeft)).apply((instance.value));
        }

        @Override
        public FlowState<S, A> visit(Either.Right<String, Trace> instance) {
          return ((forRight)).apply((instance.value));
        }
      });
    })))));
  }
  
  static java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace> pushError(String msg) {
    return (java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>) (t -> {
      String errorMsg = hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
        "Error: ",
        (msg),
        " (",
        hydra.lib.strings.Intercalate.apply(
          " > ",
          hydra.lib.lists.Reverse.apply(((t)).stack)),
        ")"));
      return new hydra.compute.Trace(((t)).stack, hydra.lib.lists.Cons.apply(
        (errorMsg),
        ((t)).messages), ((t)).other);
    });
  }
  
  static <A, S> java.util.function.Function<hydra.compute.Flow<S, A>, hydra.compute.Flow<S, A>> warn(String msg) {
    return (java.util.function.Function<hydra.compute.Flow<S, A>, hydra.compute.Flow<S, A>>) (b -> new hydra.compute.Flow((java.util.function.Function<S, java.util.function.Function<hydra.compute.Trace, hydra.compute.FlowState<S, A>>>) (s0 -> (java.util.function.Function<hydra.compute.Trace, hydra.compute.FlowState<S, A>>) (t0 -> {
      hydra.compute.FlowState<S, A> f1 = ((((b)).value).apply((s0))).apply((t0));
      java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace> addMessage = (java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>) (t -> new hydra.compute.Trace(((t)).stack, hydra.lib.lists.Cons.apply(
        hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
          "Warning: ",
          (msg))),
        ((t)).messages), ((t)).other));
      return new hydra.compute.FlowState(((f1)).value, ((f1)).state, ((addMessage)).apply(((f1)).trace));
    }))));
  }
  
  static <A, S> java.util.function.Function<hydra.compute.Flow<S, A>, hydra.compute.Flow<S, A>> withFlag(String a1) {
    java.util.function.Function<hydra.compute.Trace, java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>> restore = (java.util.function.Function<hydra.compute.Trace, java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>>) (ignored -> (java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>) (t1 -> new hydra.compute.Trace(((t1)).stack, ((t1)).messages, hydra.lib.maps.Remove.apply(
      (a1),
      ((t1)).other))));
    java.util.function.Function<hydra.compute.Trace, hydra.mantle.Either<String, Trace>> mutate = (t -> new hydra.mantle.Either.Right<>(new hydra.compute.Trace(((t)).stack, ((t)).messages, hydra.lib.maps.Insert.apply(
            (a1),
            new hydra.core.Term.Literal(new hydra.core.Literal.Boolean_(true)),
            ((t)).other))));

    Function<Function<Trace, Function<Trace, Trace>>, Function<Flow<S, A>, Flow<S, A>>> r = mutateTrace(mutate);
    return r.apply(restore);
  }
  
  static <A, S1, S2> java.util.function.Function<hydra.compute.Flow<S1, A>, hydra.compute.Flow<S2, A>> withState(S1 cx0) {
    return (f -> new hydra.compute.Flow<>((cx1 -> (t1 -> {
      hydra.compute.FlowState<S1, A> f1 = ((((f)).value).apply((cx0))).apply((t1));
      return new hydra.compute.FlowState<S2, A>(((f1)).value, (cx1), ((f1)).trace);
    }))));
  }
  
  static <A, S> java.util.function.Function<hydra.compute.Flow<S, A>, hydra.compute.Flow<S, A>> withTrace(String a1) {
    java.util.function.Function<hydra.compute.Trace, java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>> restore = (java.util.function.Function<hydra.compute.Trace, java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>>) (t0 -> (java.util.function.Function<hydra.compute.Trace, hydra.compute.Trace>) (t1 -> new hydra.compute.Trace(((t0)).stack, ((t1)).messages, ((t1)).other)));
    java.util.function.Function<hydra.compute.Trace, hydra.mantle.Either<String, hydra.compute.Trace>> mutate = (java.util.function.Function<hydra.compute.Trace, hydra.mantle.Either<String, hydra.compute.Trace>>) (t -> hydra.lib.logic.IfElse.apply(
      new hydra.mantle.Either.Left<>("maximum trace depth exceeded. This may indicate an infinite loop"),
      new hydra.mantle.Either.Right<>(new hydra.compute.Trace(hydra.lib.lists.Cons.apply(
        (a1),
        ((t)).stack), ((t)).messages, ((t)).other)),
      hydra.lib.equality.GteInt32.apply(
        hydra.lib.lists.Length.apply(((t)).stack),
        (hydra.constants.Constants.maxTraceDepth))));

    Function<Function<Trace, Function<Trace, Trace>>, Function<Flow<S, A>, Flow<S, A>>> r = mutateTrace(mutate);
    return r.apply(restore);
  }
}