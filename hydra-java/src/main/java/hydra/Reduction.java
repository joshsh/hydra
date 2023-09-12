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
import hydra.dsl.Terms;
import hydra.graph.Graph;
import hydra.tools.LList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static hydra.Common.*;
import static hydra.Flows.*;
import static hydra.extras.Extras.*;


public class Reduction {
    private Reduction() {
    }

    public static <A> Flow<Graph<A>, Term<A>> reduce(boolean eager, Term<A> term) {
        return reduce(eager, term, new HashMap<>(), null);
    }

    private static <A> Flow<Graph<A>, Term<A>> reduceArg(boolean eager, Term<A> arg) {
        // Reduce an argument only if evaluation is lazy (i.e. the argument may not already have been reduced)
        return eager ? pure(arg) : reduce(false, arg);
    }

    private static <A> Flow<Graph<A>, Term<A>> applyIfNullary(boolean eager, Term<A> original, LList<Term<A>> args) {
        return stripTerm(original).accept(new Term.PartialVisitor<A, Flow<Graph<A>, Term<A>>>() {
            @Override
            public Flow<Graph<A>, Term<A>> otherwise(Term<A> instance) {
                return pure(applyToArguments(original, args));
            }

            @Override
            public Flow<Graph<A>, Term<A>> visit(Term.Application<A> instance) {
                Application<A> app = instance.value;
                return applyIfNullary(eager, app.function, LList.push(app.argument, args));
            }

            @Override
            public Flow<Graph<A>, Term<A>> visit(Term.Function<A> instance) {
                hydra.core.Function<A> fun = instance.value;
                return fun.accept(new hydra.core.Function.Visitor<A, Flow<Graph<A>, Term<A>>>() {
                    @Override
                    public Flow<Graph<A>, Term<A>> visit(hydra.core.Function.Elimination<A> instance) {
                        if (LList.isEmpty(args)) {
                            return pure(original);
                        } else {
                            Elimination<A> elm = instance.value;
                            Term<A> arg = args.first;
                            LList<Term<A>> remainingArgs = args.rest;
                            // Reduce the argument prior to application, regardless of laziness
                            return bind(reduceArg(eager, stripTerm(arg)),
                                    reducedArg -> bind(applyElimination(elm, reducedArg),
                                            result -> bind(reduce(eager, result),
                                                    reducedResult -> applyIfNullary(eager, reducedResult,
                                                            remainingArgs))));
                        }
                    }

                    @Override
                    public Flow<Graph<A>, Term<A>> visit(hydra.core.Function.Lambda<A> instance) {
                        if (LList.isEmpty(args)) {
                            return pure(original);
                        } else {
                            Lambda<A> lam = instance.value;
                            Term<A> arg = args.first;
                            LList<Term<A>> remainingArgs = args.rest;
                            return bind(reduce(eager, stripTerm(arg)),
                                    reducedArg -> {
                                        Term<A> result = replaceFreeName(lam.parameter, reducedArg, lam.body);
                                        return bind(reduce(eager, result),
                                                reducedResult -> applyIfNullary(eager, reducedResult, remainingArgs));
                                    });
                        }
                    }

                    @Override
                    public Flow<Graph<A>, Term<A>> visit(hydra.core.Function.Primitive<A> instance) {
                        return bind(Lexical.requirePrimitive(instance.value), prim -> {
                            int arity = primitiveArity(prim);
                            if (arity <= LList.length(args)) {
                                List<Term<A>> argList = LList.take(arity, args);
                                Flow<Graph<A>, List<Term<A>>> reducedArgs = mapM(argList, a -> reduceArg(eager, a));
                                LList<Term<A>> remainingArgs = LList.drop(arity, args);
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
            public Flow<Graph<A>, Term<A>> visit(Term.Variable<A> instance) {
                // TODO: dereference variables
                return pure(applyToArguments(original, args));
            }
        });
    }

    private static <A> Flow<Graph<A>, Term<A>> applyElimination(Elimination<A> elm, Term<A> reducedArg) {
        return elm.accept(new Elimination.Visitor<A, Flow<Graph<A>, Term<A>>>() {
            @Override
            public Flow<Graph<A>, Term<A>> visit(Elimination.List<A> instance) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Flow<Graph<A>, Term<A>> visit(Elimination.Optional<A> instance) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Flow<Graph<A>, Term<A>> visit(Elimination.Product<A> instance) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Flow<Graph<A>, Term<A>> visit(Elimination.Record<A> elim) {
                return reducedArg.accept(new Term.PartialVisitor<A, Flow<Graph<A>, Term<A>>>() {
                    @Override
                    public Flow<Graph<A>, Term<A>> otherwise(Term<A> instance) {
                        return unexpected("record", instance);
                    }

                    @Override
                    public Flow<Graph<A>, Term<A>> visit(Term.Record<A> instance) {
                        Record<A> record = instance.value;
                        Projection proj = elim.value;
                        if (record.typeName.equals(proj.typeName)) {
                            for (Field<A> field : record.fields) {
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
            public Flow<Graph<A>, Term<A>> visit(Elimination.Union<A> elim) {
                return reducedArg.accept(new Term.PartialVisitor<A, Flow<Graph<A>, Term<A>>>() {
                    @Override
                    public Flow<Graph<A>, Term<A>> otherwise(Term<A> instance) {
                        return unexpected("injection", instance);
                    }

                    @Override
                    public Flow<Graph<A>, Term<A>> visit(Term.Union<A> instance) {
                        CaseStatement<A> cases = elim.value;
                        Injection<A> inj = instance.value;
                        if (cases.typeName.equals(inj.typeName)) {
                            for (Field<A> field : cases.cases) {
                                if (field.name.equals(inj.field.name)) {
                                    return pure(Terms.apply(field.term, inj.field.term));
                                }
                            }
                            return cases.default_.isPresent() ? pure(cases.default_.get())
                                : fail("no such field " + inj.field.name + " in " + cases.typeName + " case statement");
                        } else {
                            return fail("tried to match a " + inj.typeName + " injection as " + cases.typeName);
                        }
                    }
                });
            }

            @Override
            public Flow<Graph<A>, Term<A>> visit(Elimination.Wrap<A> instance) {
                return reducedArg.accept(new Term.PartialVisitor<A, Flow<Graph<A>, Term<A>>>() {
                    @Override
                    public Flow<Graph<A>, Term<A>> otherwise(Term<A> instance) {
                        return unexpected("wrapped term", instance);
                    }

                    @Override
                    public Flow<Graph<A>, Term<A>> visit(Term.Wrap<A> wrapped) {
                        Name fname = instance.value;
                        Name aname = wrapped.value.typeName;
                        return fname.equals(aname) ? pure(wrapped.value.object)
                            : fail("tried to unwrap an instance of " + aname + " as an instance of " + fname);
                    }
                });
            }
        });
    }

    private static <A> Term<A> applyToArguments(Term<A> function, LList<Term<A>> args) {
        Term<A> tcur = function;
        LList<Term<A>> lcur = args;
        while (lcur != null) {
            tcur = Terms.apply(tcur, args.first);
            lcur = lcur.rest;
        }
        return tcur;
    }

    private static <A> boolean doRecurse(boolean eager, Term<A> term) {
        boolean isLambda = term.accept(new Term.PartialVisitor<A, Boolean>() {
            @Override
            public Boolean otherwise(Term<A> instance) {
                return false;
            }

            @Override
            public Boolean visit(Term.Function<A> instance) {
                hydra.core.Function<A> fun = instance.value;
                return fun.accept(new hydra.core.Function.PartialVisitor<A, Boolean>() {
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
        });

        return eager && !isLambda;
    }

    private static <A> Flow<Graph<A>, Term<A>> reduce(boolean eager, Term<A> original, Map<Name, Term<A>> env,
        LList<Term<A>> args) {
        return Rewriting.rewriteTermM(
            new Function<Function<Term<A>, Flow<Graph<A>, Term<A>>>, Function<Term<A>, Flow<Graph<A>, Term<A>>>>() {
                @Override
                public Function<Term<A>, Flow<Graph<A>, Term<A>>> apply(
                    Function<Term<A>, Flow<Graph<A>, Term<A>>> recurse) {
                    return new Function<Term<A>, Flow<Graph<A>, Term<A>>>() {
                        @Override
                        public Flow<Graph<A>, Term<A>> apply(Term<A> mid) {
                            // Do not recurse into lambda expressions, which will cause unexpected free variables to be encountered
                            Flow<Graph<A>, Term<A>> ready = doRecurse(eager, mid) ? recurse.apply(mid) : pure(mid);
                            return bind(ready, new Function<Term<A>, Flow<Graph<A>, Term<A>>>() {
                                @Override
                                public Flow<Graph<A>, Term<A>> apply(Term<A> inner) {
                                    return applyIfNullary(eager, inner, null);
                                }
                            });
                        }
                    };
                }
            }, Flows::pure, original);
    }

    public static <A> Term<A> replaceFreeName(Name toReplace, Term<A> replacement, Term<A> body) {
        return Rewriting.rewriteTerm(recurse -> inner -> inner.accept(new Term.PartialVisitor<A, Term<A>>() {
            @Override
            public Term<A> otherwise(Term<A> instance) {
                return recurse.apply(instance);
            }

            @Override
            public Term<A> visit(Term.Function<A> instance) {
                hydra.core.Function<A> fun = instance.value;
                return fun.accept(new hydra.core.Function.PartialVisitor<A, Term<A>>() {
                    @Override
                    public Term<A> otherwise(hydra.core.Function<A> instance) {
                        return recurse.apply(inner);
                    }

                    @Override
                    public Term<A> visit(hydra.core.Function.Lambda<A> instance) {
                        Lambda<A> lam = instance.value;
                        return lam.parameter.equals(toReplace) ? inner : recurse.apply(inner);
                    }
                });
            }

            @Override
            public Term<A> visit(Term.Variable<A> instance) {
                return instance.value.equals(toReplace) ? replacement : instance;
            }
        }), a -> a, body);
    }
}