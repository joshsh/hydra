package hydra;

import hydra.compute.Flow;
import hydra.core.Application;
import hydra.core.CaseStatement;
import hydra.core.Elimination;
import hydra.core.Field;
import hydra.core.Injection;
import hydra.core.Lambda;
import hydra.core.Name;
import hydra.core.Projection;
import hydra.core.Record;
import hydra.core.Term;
import hydra.dsl.Flows;
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.LList;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static hydra.dsl.Flows.bind;
import static hydra.dsl.Flows.fail;
import static hydra.dsl.Flows.mapM;
import static hydra.dsl.Flows.pure;
import static hydra.dsl.Flows.unexpected;
import static hydra.extras.Extras.primitiveArity;
import static hydra.strip.Strip.stripTerm;


public class Reduction {
    private Reduction() {
    }

    private static  Flow<Graph, Term> applyElimination(Elimination elm, Term reducedArg) {
        return elm.accept(new Elimination.Visitor<Flow<Graph, Term>>() {
            @Override
            public Flow<Graph, Term> visit(Elimination.List instance) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Flow<Graph, Term> visit(Elimination.Optional instance) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Flow<Graph, Term> visit(Elimination.Product instance) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Flow<Graph, Term> visit(Elimination.Record elim) {
                return reducedArg.accept(new Term.PartialVisitor<Flow<Graph, Term>>() {
                    @Override
                    public Flow<Graph, Term> otherwise(Term instance) {
                        return unexpected("record", instance);
                    }

                    @Override
                    public Flow<Graph, Term> visit(Term.Record instance) {
                        Record record = instance.value;
                        Projection proj = elim.value;
                        if (record.typeName.equals(proj.typeName)) {
                            for (Field field : record.fields) {
                                if (field.name.equals(proj.field)) {
                                    return pure(field.term);
                                }
                            }
                            return fail("no such field: " + proj.field + " in " + record.typeName + " record");
                        } else {
                            return fail("tried to project a " + proj.typeName + " field out of a " + record.typeName
                                    + " record");
                        }
                    }
                });
            }

            @Override
            public Flow<Graph, Term> visit(Elimination.Union elim) {
                return reducedArg.accept(new Term.PartialVisitor<Flow<Graph, Term>>() {
                    @Override
                    public Flow<Graph, Term> otherwise(Term instance) {
                        return unexpected("injection", instance);
                    }

                    @Override
                    public Flow<Graph, Term> visit(Term.Union instance) {
                        CaseStatement cases = elim.value;
                        Injection inj = instance.value;
                        if (cases.typeName.equals(inj.typeName)) {
                            for (Field field : cases.cases) {
                                if (field.name.equals(inj.field.name)) {
                                    return pure(Terms.apply(field.term, inj.field.term));
                                }
                            }
                            return cases.default_.isPresent() ? pure(cases.default_.get())
                                    : fail("no such field " + inj.field.name
                                    + " in " + cases.typeName + " case statement");
                        } else {
                            return fail("tried to match a " + inj.typeName + " injection as " + cases.typeName);
                        }
                    }
                });
            }

            @Override
            public Flow<Graph, Term> visit(Elimination.Wrap instance) {
                return reducedArg.accept(new Term.PartialVisitor<Flow<Graph, Term>>() {
                    @Override
                    public Flow<Graph, Term> otherwise(Term instance) {
                        return unexpected("wrapped term", instance);
                    }

                    @Override
                    public Flow<Graph, Term> visit(Term.Wrap wrapped) {
                        Name fname = instance.value;
                        Name aname = wrapped.value.typeName;
                        return fname.equals(aname) ? pure(wrapped.value.object)
                                : fail("tried to unwrap an instance of " + aname + " as an instance of " + fname);
                    }
                });
            }
        });
    }

    private static  Flow<Graph, Term> applyIfNullary(boolean eager, Term original, LList<Term> args) {
        return stripTerm(original).accept(new Term.PartialVisitor<Flow<Graph, Term>>() {
            @Override
            public Flow<Graph, Term> otherwise(Term instance) {
                return pure(applyToArguments(original, args));
            }

            @Override
            public Flow<Graph, Term> visit(Term.Application instance) {
                Application app = instance.value;
                return applyIfNullary(eager, app.function, LList.push(app.argument, args));
            }

            @Override
            public Flow<Graph, Term> visit(Term.Function instance) {
                hydra.core.Function fun = instance.value;
                return fun.accept(new hydra.core.Function.Visitor<Flow<Graph, Term>>() {
                    @Override
                    public Flow<Graph, Term> visit(hydra.core.Function.Elimination instance) {
                        if (LList.isEmpty(args)) {
                            return pure(original);
                        } else {
                            Elimination elm = instance.value;
                            Term arg = args.first;
                            LList<Term> remainingArgs = args.rest;
                            // Reduce the argument prior to application, regardless of laziness
                            return bind(reduceArg(eager, stripTerm(arg)),
                                    reducedArg -> bind(applyElimination(elm, reducedArg),
                                            result -> bind(reduce(eager, result),
                                                    reducedResult -> applyIfNullary(eager, reducedResult,
                                                            remainingArgs))));
                        }
                    }

                    @Override
                    public Flow<Graph, Term> visit(hydra.core.Function.Lambda instance) {
                        if (LList.isEmpty(args)) {
                            return pure(original);
                        } else {
                            Lambda lam = instance.value;
                            Term arg = args.first;
                            LList<Term> remainingArgs = args.rest;
                            return bind(reduce(eager, stripTerm(arg)),
                                    reducedArg -> {
                                        Term result = replaceFreeName(lam.parameter, reducedArg, lam.body);
                                        return bind(reduce(eager, result),
                                                reducedResult -> applyIfNullary(eager, reducedResult, remainingArgs));
                                    });
                        }
                    }

                    @Override
                    public Flow<Graph, Term> visit(hydra.core.Function.Primitive instance) {
                        return bind(Lexical.requirePrimitive(instance.value), prim -> {
                            int arity = primitiveArity(prim);
                            if (arity <= LList.length(args)) {
                                List<Term> argList = LList.take(arity, args);
                                Flow<Graph, List<Term>> reducedArgs = mapM(argList, a -> reduceArg(eager, a));
                                LList<Term> remainingArgs = LList.drop(arity, args);
                                return bind(reducedArgs, rargs -> bind(prim.implementation.apply(rargs),
                                        result -> bind(reduce(eager, result),
                                                reducedResult -> applyIfNullary(eager, reducedResult, remainingArgs))));
                            } else {
                                // Not enough arguments available; back out
                                return pure(applyToArguments(original, args));
                            }
                        });
                    }
                });
            }

            @Override
            public Flow<Graph, Term> visit(Term.Variable instance) {
                // TODO: dereference variables
                return pure(applyToArguments(original, args));
            }
        });
    }

    private static  Term applyToArguments(Term function, LList<Term> args) {
        Term tcur = function;
        LList<Term> lcur = args;
        while (lcur != null) {
            tcur = Terms.apply(tcur, args.first);
            lcur = lcur.rest;
        }
        return tcur;
    }

    private static  boolean doRecurse(boolean eager, Term term) {
        boolean isLambda = term.accept(new Term.PartialVisitor<Boolean>() {
            @Override
            public Boolean otherwise(Term instance) {
                return false;
            }

            @Override
            public Boolean visit(Term.Function instance) {
                hydra.core.Function fun = instance.value;
                return fun.accept(new hydra.core.Function.PartialVisitor<Boolean>() {
                    @Override
                    public Boolean otherwise(hydra.core.Function instance) {
                        return false;
                    }

                    @Override
                    public Boolean visit(hydra.core.Function.Lambda instance) {
                        return true;
                    }
                });
            }
        });

        return eager && !isLambda;
    }

    public static  Flow<Graph, Term> reduce(boolean eager, Term term) {
        return reduce(eager, term, new HashMap<>(), null);
    }

    private static  Flow<Graph, Term> reduce(boolean eager,
                                                      Term original,
                                                      Map<Name, Term> env,
                                                      LList<Term> args) {
        return Rewriting.rewriteTermM(
                new Function<Function<Term, Flow<Graph, Term>>, Function<Term, Flow<Graph, Term>>>() {
                    @Override
                    public Function<Term, Flow<Graph, Term>> apply(
                            Function<Term, Flow<Graph, Term>> recurse) {
                        return new Function<Term, Flow<Graph, Term>>() {
                            @Override
                            public Flow<Graph, Term> apply(Term mid) {
                                // Do not recurse into lambda expressions,
                                // which will cause unexpected free variables to be encountered
                                Flow<Graph, Term> ready = doRecurse(eager, mid) ? recurse.apply(mid) : pure(mid);
                                return bind(ready, new Function<Term, Flow<Graph, Term>>() {
                                    @Override
                                    public Flow<Graph, Term> apply(Term inner) {
                                        return applyIfNullary(eager, inner, null);
                                    }
                                });
                            }
                        };
                    }
                }, Flows::pure, original);
    }

    private static  Flow<Graph, Term> reduceArg(boolean eager, Term arg) {
        // Reduce an argument only if evaluation is lazy (i.e. the argument may not already have been reduced)
        return eager ? pure(arg) : reduce(false, arg);
    }

    /**
     * Replace occurrences of a free variable (name) in a term with a given term.
     */
    public static  Term replaceFreeName(Name toReplace, Term replacement, Term body) {
        return Rewriting.rewriteTerm(recurse -> inner -> inner.accept(new Term.PartialVisitor<Term>() {
            @Override
            public Term otherwise(Term instance) {
                return recurse.apply(instance);
            }

            @Override
            public Term visit(Term.Function instance) {
                hydra.core.Function fun = instance.value;
                return fun.accept(new hydra.core.Function.PartialVisitor<Term>() {
                    @Override
                    public Term otherwise(hydra.core.Function instance) {
                        return recurse.apply(inner);
                    }

                    @Override
                    public Term visit(hydra.core.Function.Lambda instance) {
                        Lambda lam = instance.value;
                        return lam.parameter.equals(toReplace) ? inner : recurse.apply(inner);
                    }
                });
            }

            @Override
            public Term visit(Term.Variable instance) {
                return instance.value.equals(toReplace) ? replacement : instance;
            }
        }), a -> a, body);
    }
}