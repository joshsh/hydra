package hydra.extras;

/**
 * Basic functions which depend on primitive functions
 */
public interface Extras {
  static <A> Integer functionArity(hydra.core.Function<A> v1) {
    return ((v1)).accept(new hydra.core.Function.Visitor<A, Integer>() {
      @Override
      public Integer visit(hydra.core.Function.Elimination<A> instance) {
        return 1;
      }
      
      @Override
      public Integer visit(hydra.core.Function.Lambda<A> instance) {
        return hydra.lib.math.Add.apply(
          1,
          hydra.extras.Extras.termArity(((instance.value)).body));
      }
      
      @Override
      public Integer visit(hydra.core.Function.Primitive<A> instance) {
        return 42;
      }
    });
  }
  
  static <A> java.util.function.Function<hydra.core.Name, java.util.Optional<hydra.graph.Primitive<A>>> lookupPrimitive(hydra.graph.Graph<A> g) {
    return (java.util.function.Function<hydra.core.Name, java.util.Optional<hydra.graph.Primitive<A>>>) (name -> hydra.lib.maps.Lookup.apply(
      (name),
      ((g)).primitives));
  }
  
  static <A> Integer primitiveArity(hydra.graph.Primitive<A> x) {
    return hydra.extras.Extras.typeArity(((x)).type);
  }
  
  static java.util.function.Function<String, hydra.core.Name> qname(hydra.module.Namespace ns) {
    return (java.util.function.Function<String, hydra.core.Name>) (name -> new hydra.core.Name(hydra.lib.strings.Cat.apply(java.util.Arrays.asList(
      ((ns)).value,
      ".",
      (name)))));
  }
  
  static <A> Integer termArity(hydra.core.Term<A> v1) {
    return ((v1)).accept(new hydra.core.Term.PartialVisitor<A, Integer>() {
      @Override
      public Integer otherwise(hydra.core.Term<A> instance) {
        return 0;
      }
      
      @Override
      public Integer visit(hydra.core.Term.Application<A> instance) {
        return hydra.lib.math.Sub.apply(
          hydra.extras.Extras.termArity(((instance.value)).function),
          1);
      }
      
      @Override
      public Integer visit(hydra.core.Term.Function<A> instance) {
        return hydra.extras.Extras.functionArity((instance.value));
      }
    });
  }
  
  static <A> Integer typeArity(hydra.core.Type<A> v1) {
    return ((v1)).accept(new hydra.core.Type.PartialVisitor<A, Integer>() {
      @Override
      public Integer otherwise(hydra.core.Type<A> instance) {
        return 0;
      }
      
      @Override
      public Integer visit(hydra.core.Type.Annotated<A> instance) {
        return hydra.extras.Extras.typeArity(((instance.value)).subject);
      }
      
      @Override
      public Integer visit(hydra.core.Type.Application<A> instance) {
        return hydra.extras.Extras.typeArity(((instance.value)).function);
      }
      
      @Override
      public Integer visit(hydra.core.Type.Lambda<A> instance) {
        return hydra.extras.Extras.typeArity(((instance.value)).body);
      }
      
      @Override
      public Integer visit(hydra.core.Type.Function<A> instance) {
        return hydra.lib.math.Add.apply(
          1,
          hydra.extras.Extras.typeArity(((instance.value)).codomain));
      }
    });
  }
  
  hydra.compute.Kv emptyKv = new hydra.compute.Kv(hydra.lib.maps.Empty.apply());
  
  static java.util.function.Function<hydra.compute.Kv, java.util.Optional<hydra.core.Term<hydra.compute.Kv>>> getAnnotation(String key) {
    return (java.util.function.Function<hydra.compute.Kv, java.util.Optional<hydra.core.Term<hydra.compute.Kv>>>) (ann -> hydra.lib.maps.Lookup.apply(
      (key),
      ((ann)).annotations));
  }
}