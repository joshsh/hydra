// Note: this is an automatically generated file. Do not edit.

package hydra.graph;

/**
 * A typeclass-like construct providing common functions for working with annotations
 */
public class AnnotationClass<A> {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/graph.AnnotationClass");
  
  public final A default_;
  
  public final java.util.function.Function<A, java.util.function.Function<A, Boolean>> equal;
  
  public final java.util.function.Function<A, java.util.function.Function<A, hydra.graph.Comparison>> compare;
  
  public final java.util.function.Function<A, String> show;
  
  public final java.util.function.Function<String, hydra.util.Opt<A>> read;
  
  public final java.util.function.Function<hydra.core.Term<A>, A> termAnnotation;
  
  public final java.util.function.Function<hydra.core.Type<A>, A> typeAnnotation;
  
  public final java.util.function.Function<hydra.core.Term<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<String>>> termDescription;
  
  public final java.util.function.Function<hydra.core.Type<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<String>>> typeDescription;
  
  public final java.util.function.Function<hydra.core.Type<A>, hydra.compute.Flow<hydra.graph.Graph<A>, java.util.Map<hydra.core.Name, java.util.Set<hydra.graph.TypeClass>>>> typeClasses;
  
  public final java.util.function.Function<hydra.core.Term<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<hydra.core.Type<A>>>> termType;
  
  public final java.util.function.Function<hydra.util.Opt<String>, java.util.function.Function<hydra.core.Term<A>, hydra.core.Term<A>>> setTermDescription;
  
  public final java.util.function.Function<hydra.util.Opt<hydra.core.Type<A>>, java.util.function.Function<hydra.core.Term<A>, hydra.core.Term<A>>> setTermType;
  
  public final java.util.function.Function<java.util.Map<hydra.core.Name, java.util.Set<hydra.graph.TypeClass>>, java.util.function.Function<hydra.core.Type<A>, hydra.core.Type<A>>> setTypeClasses;
  
  public final java.util.function.Function<A, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<hydra.core.Type<A>>>> typeOf;
  
  public final java.util.function.Function<hydra.util.Opt<hydra.core.Type<A>>, java.util.function.Function<A, A>> setTypeOf;
  
  public AnnotationClass (A default_, java.util.function.Function<A, java.util.function.Function<A, Boolean>> equal, java.util.function.Function<A, java.util.function.Function<A, hydra.graph.Comparison>> compare, java.util.function.Function<A, String> show, java.util.function.Function<String, hydra.util.Opt<A>> read, java.util.function.Function<hydra.core.Term<A>, A> termAnnotation, java.util.function.Function<hydra.core.Type<A>, A> typeAnnotation, java.util.function.Function<hydra.core.Term<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<String>>> termDescription, java.util.function.Function<hydra.core.Type<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<String>>> typeDescription, java.util.function.Function<hydra.core.Type<A>, hydra.compute.Flow<hydra.graph.Graph<A>, java.util.Map<hydra.core.Name, java.util.Set<hydra.graph.TypeClass>>>> typeClasses, java.util.function.Function<hydra.core.Term<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<hydra.core.Type<A>>>> termType, java.util.function.Function<hydra.util.Opt<String>, java.util.function.Function<hydra.core.Term<A>, hydra.core.Term<A>>> setTermDescription, java.util.function.Function<hydra.util.Opt<hydra.core.Type<A>>, java.util.function.Function<hydra.core.Term<A>, hydra.core.Term<A>>> setTermType, java.util.function.Function<java.util.Map<hydra.core.Name, java.util.Set<hydra.graph.TypeClass>>, java.util.function.Function<hydra.core.Type<A>, hydra.core.Type<A>>> setTypeClasses, java.util.function.Function<A, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<hydra.core.Type<A>>>> typeOf, java.util.function.Function<hydra.util.Opt<hydra.core.Type<A>>, java.util.function.Function<A, A>> setTypeOf) {
    java.util.Objects.requireNonNull((default_));
    java.util.Objects.requireNonNull((equal));
    java.util.Objects.requireNonNull((compare));
    java.util.Objects.requireNonNull((show));
    java.util.Objects.requireNonNull((read));
    java.util.Objects.requireNonNull((termAnnotation));
    java.util.Objects.requireNonNull((typeAnnotation));
    java.util.Objects.requireNonNull((termDescription));
    java.util.Objects.requireNonNull((typeDescription));
    java.util.Objects.requireNonNull((typeClasses));
    java.util.Objects.requireNonNull((termType));
    java.util.Objects.requireNonNull((setTermDescription));
    java.util.Objects.requireNonNull((setTermType));
    java.util.Objects.requireNonNull((setTypeClasses));
    java.util.Objects.requireNonNull((typeOf));
    java.util.Objects.requireNonNull((setTypeOf));
    this.default_ = default_;
    this.equal = equal;
    this.compare = compare;
    this.show = show;
    this.read = read;
    this.termAnnotation = termAnnotation;
    this.typeAnnotation = typeAnnotation;
    this.termDescription = termDescription;
    this.typeDescription = typeDescription;
    this.typeClasses = typeClasses;
    this.termType = termType;
    this.setTermDescription = setTermDescription;
    this.setTermType = setTermType;
    this.setTypeClasses = setTypeClasses;
    this.typeOf = typeOf;
    this.setTypeOf = setTypeOf;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnnotationClass)) {
      return false;
    }
    AnnotationClass o = (AnnotationClass) (other);
    return default_.equals(o.default_) && equal.equals(o.equal) && compare.equals(o.compare) && show.equals(o.show) && read.equals(o.read) && termAnnotation.equals(o.termAnnotation) && typeAnnotation.equals(o.typeAnnotation) && termDescription.equals(o.termDescription) && typeDescription.equals(o.typeDescription) && typeClasses.equals(o.typeClasses) && termType.equals(o.termType) && setTermDescription.equals(o.setTermDescription) && setTermType.equals(o.setTermType) && setTypeClasses.equals(o.setTypeClasses) && typeOf.equals(o.typeOf) && setTypeOf.equals(o.setTypeOf);
  }
  
  @Override
  public int hashCode() {
    return 2 * default_.hashCode() + 3 * equal.hashCode() + 5 * compare.hashCode() + 7 * show.hashCode() + 11 * read.hashCode() + 13 * termAnnotation.hashCode() + 17 * typeAnnotation.hashCode() + 19 * termDescription.hashCode() + 23 * typeDescription.hashCode() + 29 * typeClasses.hashCode() + 31 * termType.hashCode() + 37 * setTermDescription.hashCode() + 41 * setTermType.hashCode() + 43 * setTypeClasses.hashCode() + 47 * typeOf.hashCode() + 53 * setTypeOf.hashCode();
  }
  
  public AnnotationClass withDefault(A default_) {
    java.util.Objects.requireNonNull((default_));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withEqual(java.util.function.Function<A, java.util.function.Function<A, Boolean>> equal) {
    java.util.Objects.requireNonNull((equal));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withCompare(java.util.function.Function<A, java.util.function.Function<A, hydra.graph.Comparison>> compare) {
    java.util.Objects.requireNonNull((compare));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withShow(java.util.function.Function<A, String> show) {
    java.util.Objects.requireNonNull((show));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withRead(java.util.function.Function<String, hydra.util.Opt<A>> read) {
    java.util.Objects.requireNonNull((read));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withTermAnnotation(java.util.function.Function<hydra.core.Term<A>, A> termAnnotation) {
    java.util.Objects.requireNonNull((termAnnotation));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withTypeAnnotation(java.util.function.Function<hydra.core.Type<A>, A> typeAnnotation) {
    java.util.Objects.requireNonNull((typeAnnotation));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withTermDescription(java.util.function.Function<hydra.core.Term<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<String>>> termDescription) {
    java.util.Objects.requireNonNull((termDescription));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withTypeDescription(java.util.function.Function<hydra.core.Type<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<String>>> typeDescription) {
    java.util.Objects.requireNonNull((typeDescription));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withTypeClasses(java.util.function.Function<hydra.core.Type<A>, hydra.compute.Flow<hydra.graph.Graph<A>, java.util.Map<hydra.core.Name, java.util.Set<hydra.graph.TypeClass>>>> typeClasses) {
    java.util.Objects.requireNonNull((typeClasses));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withTermType(java.util.function.Function<hydra.core.Term<A>, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<hydra.core.Type<A>>>> termType) {
    java.util.Objects.requireNonNull((termType));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withSetTermDescription(java.util.function.Function<hydra.util.Opt<String>, java.util.function.Function<hydra.core.Term<A>, hydra.core.Term<A>>> setTermDescription) {
    java.util.Objects.requireNonNull((setTermDescription));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withSetTermType(java.util.function.Function<hydra.util.Opt<hydra.core.Type<A>>, java.util.function.Function<hydra.core.Term<A>, hydra.core.Term<A>>> setTermType) {
    java.util.Objects.requireNonNull((setTermType));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withSetTypeClasses(java.util.function.Function<java.util.Map<hydra.core.Name, java.util.Set<hydra.graph.TypeClass>>, java.util.function.Function<hydra.core.Type<A>, hydra.core.Type<A>>> setTypeClasses) {
    java.util.Objects.requireNonNull((setTypeClasses));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withTypeOf(java.util.function.Function<A, hydra.compute.Flow<hydra.graph.Graph<A>, hydra.util.Opt<hydra.core.Type<A>>>> typeOf) {
    java.util.Objects.requireNonNull((typeOf));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
  
  public AnnotationClass withSetTypeOf(java.util.function.Function<hydra.util.Opt<hydra.core.Type<A>>, java.util.function.Function<A, A>> setTypeOf) {
    java.util.Objects.requireNonNull((setTypeOf));
    return new AnnotationClass(default_, equal, compare, show, read, termAnnotation, typeAnnotation, termDescription, typeDescription, typeClasses, termType, setTermDescription, setTermType, setTypeClasses, typeOf, setTypeOf);
  }
}