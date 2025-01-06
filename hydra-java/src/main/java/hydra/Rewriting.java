package hydra;

import hydra.compute.Flow;
import hydra.core.AnnotatedTerm;
import hydra.core.Application;
import hydra.core.CaseStatement;
import hydra.core.Elimination;
import hydra.core.Field;
import hydra.core.Injection;
import hydra.core.Lambda;
import hydra.core.Let;
import hydra.core.LetBinding;
import hydra.core.Name;
import hydra.core.OptionalCases;
import hydra.core.Projection;
import hydra.core.Record;
import hydra.core.Sum;
import hydra.core.Term;
import hydra.core.TypedTerm;
import hydra.core.Unit;
import hydra.core.WrappedTerm;
import hydra.dsl.Flows;
import hydra.dsl.Terms;
import hydra.util.Opt;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Function;

import static hydra.dsl.Flows.*;


/**
 * Utility functions for rewriting terms, types, and other recursive data structures.
 */
public interface Rewriting {
    /**
     * A generic rewriting function, suitable for many recursive data structures.
     */
    static <X, Y> Function<X, Y> rewrite(Function<Function<X, Y>, Function<X, Y>> fsub,
                                         Function<Function<X, Y>, Function<X, Y>> f) {
        final AtomicReference<Function<X, Y>> ref = new AtomicReference<>();
        ref.set(f.apply(fsub.apply(x -> ref.get().apply(x))));
        return ref.get();
    }

    /**
     * Rewrite an elimination expression using a monadic function.
     */
    static <S> Flow<S, Elimination> rewriteEliminationM(Function<Term, Flow<S, Term>> recurse,
                                                                 Elimination original) {
        return original.accept(new Elimination.Visitor<Flow<S, Elimination>>() {
            @Override
            public Flow<S, Elimination> visit(Elimination.List instance) {
                // TODO: this is incorrect in Hydra Core
                Term foldA = instance.value;
                return map(recurse.apply(foldA), Elimination.List::new);
            }

            @Override
            public Flow<S, Elimination> visit(Elimination.Optional instance) {
                OptionalCases foldA = instance.value;
                return map2(recurse.apply(foldA.nothing), recurse.apply(foldA.just),
                        (n, j) -> new Elimination.Optional(new OptionalCases(n, j)));
            }

            @Override
            public Flow<S, Elimination> visit(Elimination.Product instance) {
                return pure(new Elimination.Product(instance.value));
            }

            @Override
            public Flow<S, Elimination> visit(Elimination.Record instance) {
                return pure(new Elimination.Record(new Projection(instance.value.typeName, instance.value.field)));
            }

            @Override
            public Flow<S, Elimination> visit(Elimination.Union instance) {
                CaseStatement caseA = instance.value;
                Flow<S, CaseStatement> caseB =
                        map2(mapM(caseA.default_, recurse), mapM(caseA.cases, f -> rewriteFieldM(recurse, f)),
                                (def, fields) -> new CaseStatement(instance.value.typeName, def, fields));
                return map(caseB, Elimination.Union::new);
            }

            @Override
            public Flow<S, Elimination> visit(Elimination.Wrap instance) {
                return pure(new Elimination.Wrap(instance.value));
            }
        });
    }

    /**
     * Rewrite a field using a monadic function.
     */
    static <S> Flow<S, Field> rewriteFieldM(Function<Term, Flow<S, Term>> recurse, Field original) {
        return map(recurse.apply(original.term), term -> new Field(original.name, term));
    }

    /**
     * Rewrite a function expression using a monadic function.
     */
    static <S> Flow<S, hydra.core.Function> rewriteFunctionM(Function<Term, Flow<S, Term>> recurse,
                                                                      hydra.core.Function original) {
        return original.accept(new hydra.core.Function.Visitor<Flow<S, hydra.core.Function>>() {
            @Override
            public Flow<S, hydra.core.Function> visit(hydra.core.Function.Elimination instance) {
                Elimination elimA = instance.value;
                return map(rewriteEliminationM(recurse, elimA), hydra.core.Function.Elimination::new);
            }

            @Override
            public Flow<S, hydra.core.Function> visit(hydra.core.Function.Lambda instance) {
                Term bodyA = instance.value.body;
                return map(recurse.apply(bodyA),
                        term -> new hydra.core.Function.Lambda(
                                new Lambda(instance.value.parameter, Opt.empty(), term)));
            }

            @Override
            public Flow<S, hydra.core.Function> visit(hydra.core.Function.Primitive instance) {
                return pure(new hydra.core.Function.Primitive(instance.value));
            }
        });
    }

    /**
     * This is a workaround for a non-monadic rewriting function; the latter would be more efficient.
     */
    static Term rewriteTerm(Function<Function<Term, Term>, Function<Term, Term>> f,
                                      Function<Map<Name, Term>, Map<Name, Term>> mf, Term original) {
        Function<Function<Term, Flow<Unit, Term>>, Function<Term, Flow<Unit, Term>>> fflow =
                recurse -> (Function<Term, Flow<Unit, Term>>) term -> {
                    Term result = f.apply(t -> fromFlow(Flows.UNIT, recurse.apply(t))).apply(term);
                    return pure(result);
                };

        Function<Map<Name, Term>, Flow<Unit, Map<Name, Term>>> mfflow = a -> pure(mf.apply(a));
        return fromFlow(Flows.UNIT, rewriteTermM(fflow, mfflow, original));
    }

    /**
     * Rewrite a term using a monadic function.
     */
    static <S> Flow<S, Term> rewriteTermM(
            Function<Function<Term, Flow<S, Term>>, Function<Term, Flow<S, Term>>> f,
            Function<Map<Name, Term>, Flow<S, Map<Name, Term>>> mf,
            Term original) {
        Function<Function<Term, Flow<S, Term>>, Function<Term, Flow<S, Term>>> fsub =
                recurse -> term -> term.accept(new Term.Visitor<Flow<S, Term>>() {
                    @Override
                    public Flow<S, Term> visit(Term.Annotated instance) {
                        AnnotatedTerm ann = instance.value;
                        return map2(recurse.apply(ann.subject), mf.apply(ann.annotation),
                                (term1, ann1) -> Terms.annot(ann1, term1));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Application instance) {
                        Term funA = instance.value.function;
                        Term argA = instance.value.argument;
                        return map2(recurse.apply(funA), recurse.apply(argA),
                                (f1, a) -> new Term.Application(new Application(f1, a)));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Function instance) {
                        hydra.core.Function funA = instance.value;
                        return map(rewriteFunctionM(recurse, funA), Term.Function::new);
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Let instance) {
                        List<LetBinding> bindingsA = instance.value.bindings;
                        Term envA = instance.value.environment;
                        Flow<S, List<LetBinding>> bindingsB = mapM(bindingsA,
                            b -> Flows.map(recurse.apply(b.term), b::withTerm));
                        Flow<S, Term> envB = recurse.apply(envA);
                        return map2(bindingsB, envB, (b, e) -> new Term.Let(new Let(b, e)));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.List instance) {
                        List<Term> termsA = instance.value;
                        Flow<S, List<Term>> termsB = mapM(termsA, recurse);
                        return map(termsB, Term.List::new);
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Literal instance) {
                        return pure(new Term.Literal(instance.value));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Map instance) {
                        Map<Term, Term> mapA = instance.value;
                        Flow<S, Map<Term, Term>> mapB = mapM(mapA, recurse, recurse);
                        return map(mapB, Term.Map::new);
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Optional instance) {
                        Opt<Term> termA = instance.value;
                        Flow<S, Opt<Term>> termB = mapM(termA, recurse);
                        return map(termB, Term.Optional::new);
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Product instance) {
                        List<Term> termsA = instance.value;
                        Flow<S, List<Term>> termsB = mapM(termsA, recurse);
                        return map(termsB, Term.Product::new);
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Record instance) {
                        List<Field> fieldsA = instance.value.fields;
                        Flow<S, List<Field>> fieldsB = mapM(fieldsA, field -> rewriteFieldM(recurse, field));
                        return map(fieldsB,
                                fields -> new Term.Record(new Record(instance.value.typeName, fields)));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Set instance) {
                        Flow<S, Set<Term>> els = mapM(instance.value, recurse);
                        return map(els, Term.Set::new);
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Sum instance) {
                        Term t0 = instance.value.term;
                        Flow<S, Term> t1 = recurse.apply(t0);
                        return map(t1, t2 -> new Term.Sum(
                                new Sum(instance.value.index, instance.value.size, t2)));
                    }

                  @Override
                  public Flow<S, Term> visit(Term.TypeAbstraction instance) {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                  public Flow<S, Term> visit(Term.TypeApplication instance) {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                    public Flow<S, Term> visit(Term.Typed instance) {
                        Term t0 = instance.value.term;
                        Flow<S, Term> t1 = recurse.apply(t0);
                        return map(t1, t2 -> new Term.Typed(new TypedTerm(t2, instance.value.type)));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Union instance) {
                        Flow<S, Field> t = rewriteFieldM(recurse, instance.value.field);
                        return map(t, field -> new Term.Union(new Injection(instance.value.typeName, field)));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Variable instance) {
                        return pure(new Term.Variable(instance.value));
                    }

                    @Override
                    public Flow<S, Term> visit(Term.Wrap instance) {
                        Flow<S, Term> obj2 = recurse.apply(instance.value.object);
                        return map(obj2, term -> new Term.Wrap(new WrappedTerm(instance.value.typeName, term)));
                    }
                });
        return rewrite(fsub, f).apply(original);
    }
}
