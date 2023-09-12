package hydra;

import hydra.compute.Flow;
import hydra.core.Annotated;
import hydra.core.Application;
import hydra.core.CaseStatement;
import hydra.core.Elimination;
import hydra.core.Field;
import hydra.core.Injection;
import hydra.core.Lambda;
import hydra.core.Let;
import hydra.core.Name;
import hydra.core.Nominal;
import hydra.core.OptionalCases;
import hydra.core.Projection;
import hydra.core.Record;
import hydra.core.Sum;
import hydra.core.Term;
import hydra.dsl.Terms;

import static hydra.Flows.*;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Function;


public interface Rewriting {
    static <X, Y> Function<X, Y> rewrite(Function<Function<X, Y>, Function<X, Y>> fsub,
        Function<Function<X, Y>, Function<X, Y>> f) {
        final AtomicReference<Function<X, Y>> ref = new AtomicReference<>();
        ref.set(f.apply(fsub.apply(x -> ref.get().apply(x))));
        return ref.get();
    }

    static <A, B, S> Flow<S, Elimination<B>> rewriteEliminationM(Function<Term<A>, Flow<S, Term<B>>> recurse,
        Elimination<A> original) {
        return original.accept(new Elimination.Visitor<A, Flow<S, Elimination<B>>>() {
            @Override
            public Flow<S, Elimination<B>> visit(Elimination.List<A> instance) {
                // TODO: this is incorrect in Hydra Core
                Term<A> foldA = instance.value;
                return map(recurse.apply(foldA), Elimination.List::new);
            }

            @Override
            public Flow<S, Elimination<B>> visit(Elimination.Optional<A> instance) {
                OptionalCases<A> foldA = instance.value;
                return map2(recurse.apply(foldA.nothing), recurse.apply(foldA.just),
                        (n, j) -> new Elimination.Optional<>(new OptionalCases<>(n, j)));
            }

            @Override
            public Flow<S, Elimination<B>> visit(Elimination.Product<A> instance) {
                return pure(new Elimination.Product<B>(instance.value));
            }

            @Override
            public Flow<S, Elimination<B>> visit(Elimination.Record<A> instance) {
                return pure(new Elimination.Record<>(new Projection(instance.value.typeName, instance.value.field)));
            }

            @Override
            public Flow<S, Elimination<B>> visit(Elimination.Union<A> instance) {
                CaseStatement<A> caseA = instance.value;
                Flow<S, CaseStatement<B>> caseB =
                        map2(mapM(caseA.default_, recurse), mapM(caseA.cases, f -> rewriteFieldM(recurse, f)),
                                (def, fields) -> new CaseStatement<>(instance.value.typeName, def, fields));
                return map(caseB, Elimination.Union::new);
            }

            @Override
            public Flow<S, Elimination<B>> visit(Elimination.Wrap<A> instance) {
                return pure(new Elimination.Wrap<>(instance.value));
            }
        });
    }

    static <A, B, S> Flow<S, Field<B>> rewriteFieldM(Function<Term<A>, Flow<S, Term<B>>> recurse, Field<A> original) {
        return map(recurse.apply(original.term), bTerm -> new Field<>(original.name, bTerm));
    }

    static <A, B, S> Flow<S, hydra.core.Function<B>> rewriteFunctionM(Function<Term<A>, Flow<S, Term<B>>> recurse,
        hydra.core.Function<A> original) {
        return original.accept(new hydra.core.Function.Visitor<A, Flow<S, hydra.core.Function<B>>>() {
            @Override
            public Flow<S, hydra.core.Function<B>> visit(hydra.core.Function.Elimination<A> instance) {
                Elimination<A> elimA = instance.value;
                return map(rewriteEliminationM(recurse, elimA), hydra.core.Function.Elimination::new);
            }

            @Override
            public Flow<S, hydra.core.Function<B>> visit(hydra.core.Function.Lambda<A> instance) {
                Term<A> bodyA = instance.value.body;
                return map(recurse.apply(bodyA),
                        bTerm -> new hydra.core.Function.Lambda<B>(new Lambda<>(instance.value.parameter, bTerm)));
            }

            @Override
            public Flow<S, hydra.core.Function<B>> visit(hydra.core.Function.Primitive<A> instance) {
                return pure(new hydra.core.Function.Primitive<>(instance.value));
            }
        });
    }

    // This is a workaround for a non-monadic rewriting function; the latter would be more efficient
    static <A, B> Term<B> rewriteTerm(Function<Function<Term<A>, Term<B>>, Function<Term<A>, Term<B>>> f,
        Function<A, B> mf, Term<A> original) {
        Function<Function<Term<A>, Flow<Boolean, Term<B>>>, Function<Term<A>, Flow<Boolean, Term<B>>>> fFlow =
            recurse -> (Function<Term<A>, Flow<Boolean, Term<B>>>) term -> {
                Term<B> result = f.apply(t -> fromFlow(null, null, recurse.apply(t))).apply(term);
                return pure(result);
            };

        Function<A, Flow<Boolean, B>> mfFlow = a -> pure(mf.apply(a));
        return fromFlow(null, null, rewriteTermM(fFlow, mfFlow, original));
    }

    static <A, B, S> Flow<S, Term<B>> rewriteTermM(
        Function<Function<Term<A>, Flow<S, Term<B>>>, Function<Term<A>, Flow<S, Term<B>>>> f,
        Function<A, Flow<S, B>> mf, Term<A> original) {
        Function<Function<Term<A>, Flow<S, Term<B>>>, Function<Term<A>, Flow<S, Term<B>>>> fsub =
            recurse -> term -> term.accept(new Term.Visitor<A, Flow<S, Term<B>>>() {
                @Override
                public Flow<S, Term<B>> visit(Term.Annotated<A> instance) {
                    Annotated<Term<A>, A> ann = instance.value;
                    return map2(recurse.apply(ann.subject), mf.apply(ann.annotation),
                        (term1, ann1) -> Terms.annot(ann1, term1));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Application<A> instance) {
                    Term<A> funA = instance.value.function;
                    Term<A> argA = instance.value.argument;
                    return map2(recurse.apply(funA), recurse.apply(argA),
                        (f1, a) -> new Term.Application<>(new Application<>(f1, a)));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Function<A> instance) {
                    hydra.core.Function<A> funA = instance.value;
                    return map(rewriteFunctionM(recurse, funA), Term.Function::new);
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Let<A> instance) {
                    Map<Name, Term<A>> bindingsA = instance.value.bindings;
                    Term<A> envA = instance.value.environment;
                    Flow<S, Map<Name, Term<B>>> bindingsB = mapM(bindingsA, Flows::pure, recurse);
                    Flow<S, Term<B>> envB = recurse.apply(envA);
                    return map2(bindingsB, envB, (b, e) -> new Term.Let<>(new Let<>(b, e)));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.List<A> instance) {
                    List<Term<A>> termsA = instance.value;
                    Flow<S, List<Term<B>>> termsB = mapM(termsA, recurse);
                    return map(termsB, Term.List::new);
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Literal<A> instance) {
                    return pure(new Term.Literal<>(instance.value));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Map<A> instance) {
                    Map<Term<A>, Term<A>> mapA = instance.value;
                    Flow<S, Map<Term<B>, Term<B>>> mapB = mapM(mapA, recurse, recurse);
                    return map(mapB, Term.Map::new);
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Optional<A> instance) {
                    Optional<Term<A>> termA = instance.value;
                    Flow<S, Optional<Term<B>>> termB = mapM(termA, recurse);
                    return map(termB, Term.Optional::new);
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Product<A> instance) {
                    List<Term<A>> termsA = instance.value;
                    Flow<S, List<Term<B>>> termsB = mapM(termsA, recurse);
                    return map(termsB, Term.Product::new);
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Record<A> instance) {
                    List<Field<A>> fieldsA = instance.value.fields;
                    Flow<S, List<Field<B>>> fieldsB = mapM(fieldsA, aField -> rewriteFieldM(recurse, aField));
                    return map(fieldsB, fields -> new Term.Record<>(new Record<>(instance.value.typeName, fields)));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Set<A> instance) {
                    Flow<S, Set<Term<B>>> els = mapM(instance.value, recurse);
                    return map(els, Term.Set::new);
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Stream<A> instance) {
                    throw new UnsupportedOperationException();
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Sum<A> instance) {
                    Term<A> t0 = instance.value.term;
                    Flow<S, Term<B>> t1 = recurse.apply(t0);
                    return map(t1, t2 -> new Term.Sum<B>(new Sum<B>(instance.value.index, instance.value.size, t2)));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Union<A> instance) {
                    Flow<S, Field<B>> t = rewriteFieldM(recurse, instance.value.field);
                    return map(t, bField -> new Term.Union<>(new Injection<>(instance.value.typeName, bField)));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Variable<A> instance) {
                    return pure(new Term.Variable<B>(instance.value));
                }

                @Override
                public Flow<S, Term<B>> visit(Term.Wrap<A> instance) {
                    Flow<S, Term<B>> obj2 = recurse.apply(instance.value.object);
                    return map(obj2, bTerm -> new Term.Wrap<>(new Nominal<>(instance.value.typeName, bTerm)));
                }
            });
        return rewrite(fsub, f).apply(original);
    }
}
