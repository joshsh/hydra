package hydra;

import hydra.core.Term;
import hydra.core.Type;


public interface Common {
    static <A> Term<A> stripTerm(Term<A> term) {
        return term.accept(new Term.PartialVisitor<A, Term<A>>() {
            @Override
            public Term<A> otherwise(Term<A> ignored) {
                return term;
            }

            @Override
            public Term<A> visit(Term.Annotated<A> instance) {
                return stripTerm(instance.value.subject);
            }
        });
    }

    static <A> Type<A> stripType(Type<A> type) {
        return type.accept(new Type.PartialVisitor<A, Type<A>>() {
            @Override
            public Type<A> otherwise(Type<A> ignored) {
                return type;
            }

            @Override
            public Type<A> visit(Type.Annotated<A> instance) {
                return stripType(instance.value.subject);
            }
        });
    }
}
