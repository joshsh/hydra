package hydra.strip;

/**
 * Several functions for stripping annotations from types and terms.
 */
public interface Strip {
  static <A, X> java.util.function.Function<X, X> skipAnnotations(java.util.function.Function<X, java.util.Optional<hydra.core.Annotated<X, A>>> getAnn) {
    return (java.util.function.Function<X, X>) (t -> {
      java.util.concurrent.atomic.AtomicReference<java.util.function.Function<X, X>> skip = new java.util.concurrent.atomic.AtomicReference<>();
      skip.set((java.util.function.Function<X, X>) (t1 -> ((((getAnn)).apply((t1))).map((java.util.function.Function<hydra.core.Annotated<X, A>, X>) (ann -> (skip.get()).apply(((ann)).subject)))).orElse((t1))));
      return ((skip)).get().apply((t));
    });
  }
  
  static <A> hydra.core.Term<A> stripTerm(hydra.core.Term<A> x) {
    return (hydra.strip.Strip.skipAnnotations((java.util.function.Function<hydra.core.Term<A>, java.util.Optional<hydra.core.Annotated<hydra.core.Term<A>, A>>>) (v1 -> ((v1)).accept(new hydra.core.Term.PartialVisitor<A, java.util.Optional<hydra.core.Annotated<hydra.core.Term<A>, A>>>() {
      @Override
      public java.util.Optional<hydra.core.Annotated<hydra.core.Term<A>, A>> otherwise(hydra.core.Term<A> instance) {
        return java.util.Optional.empty();
      }
      
      @Override
      public java.util.Optional<hydra.core.Annotated<hydra.core.Term<A>, A>> visit(hydra.core.Term.Annotated<A> instance) {
        return java.util.Optional.of((instance.value));
      }
    })))).apply((x));
  }
  
  static <A> hydra.core.Type<A> stripType(hydra.core.Type<A> x) {
    return (hydra.strip.Strip.skipAnnotations((java.util.function.Function<hydra.core.Type<A>, java.util.Optional<hydra.core.Annotated<hydra.core.Type<A>, A>>>) (v1 -> ((v1)).accept(new hydra.core.Type.PartialVisitor<A, java.util.Optional<hydra.core.Annotated<hydra.core.Type<A>, A>>>() {
      @Override
      public java.util.Optional<hydra.core.Annotated<hydra.core.Type<A>, A>> otherwise(hydra.core.Type<A> instance) {
        return java.util.Optional.empty();
      }
      
      @Override
      public java.util.Optional<hydra.core.Annotated<hydra.core.Type<A>, A>> visit(hydra.core.Type.Annotated<A> instance) {
        return java.util.Optional.of((instance.value));
      }
    })))).apply((x));
  }
  
  static <A> hydra.core.Type<A> stripTypeParameters(hydra.core.Type<A> t) {
    return (hydra.strip.Strip.stripType((t))).accept(new hydra.core.Type.PartialVisitor<A, hydra.core.Type<A>>() {
      @Override
      public hydra.core.Type<A> otherwise(hydra.core.Type<A> instance) {
        return (t);
      }
      
      @Override
      public hydra.core.Type<A> visit(hydra.core.Type.Lambda<A> instance) {
        return hydra.strip.Strip.stripTypeParameters(((instance.value)).body);
      }
    });
  }
}