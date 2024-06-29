package hydra.dsl;

import hydra.compute.FlowState;
import hydra.core.Annotated;
import hydra.core.Application;
import hydra.core.CaseStatement;
import hydra.core.Elimination;
import hydra.core.Field;
import hydra.core.Name;
import hydra.core.FloatValue;
import hydra.core.Function;
import hydra.core.Injection;
import hydra.core.IntegerValue;
import hydra.core.Lambda;
import hydra.core.Let;
import hydra.core.Literal;
import hydra.core.Name;
import hydra.core.OptionalCases;
import hydra.core.Projection;
import hydra.core.Record;
import hydra.core.Term;
import hydra.core.Tuple;
import hydra.core.UnitType;

import hydra.core.Nominal;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static hydra.dsl.Core.*;


public interface Terms {
    static <A> Term<A> annot(final A ann, final Term<A> base) {
        return new Term.Annotated<>(new Annotated<>(base, ann));
    }

    static <A> Term<A> apply(final Term<A> lhs, final Term<A>... rhs) {
        Term<A> cur = lhs;
        for (Term<A> r : rhs) {
            cur = new Term.Application<>(new Application<>(lhs, r));
        }
        return cur;
    }

    static <A> Term<A> app(final Term<A> lhs, final Term<A>... rhs) {
        return apply(lhs, rhs);
    }

    static <A> Term<A> app(final String lhs, final Term<A>... rhs) {
        return apply(variable(lhs), rhs);
    }

    static <A> Term<A> bigfloat(final double value) {
        return literal(Literals.bigfloat(value));
    }

    static <A> Term<A> bigint(final BigInteger value) {
        return literal(Literals.bigint(value));
    }

    static <A> Term<A> binary(final String value) {
        return literal(Literals.binary(value));
    }

    static <A> Term<A> boolean_(final boolean value) {
        return literal(Literals.boolean_(value));
    }

    static <A> Term<A> cases(final Name name, final Optional<Term<A>> def, final Field<A>... fields) {
        return elimination(new Elimination.Union<>(new CaseStatement<>(name, def, Arrays.asList(fields))));
    }

    static <A> Term<A> elimination(final Elimination<A> elim) {
        return function(new Function.Elimination<>(elim));
    }

    static <A> Field<A> field(final String fname, final Term<A> term) {
        return new Field<>(new Name(fname), term);
    }

    static <A> Field<A> field(final String fname, final String term) {
        return field(fname, variable(term));
    }

    static <A> Term<A> float_(final FloatValue value) {
        return literal(Literals.float_(value));
    }

    static <A> Term<A> float32(final float value) {
        return literal(Literals.float32(value));
    }

    static <A> Term<A> float64(final double value) {
        return literal(Literals.float64(value));
    }

    static <A> Term<A> flowState(Term<A> value, Term<A> state, Term<A> trace) {
        return record(FlowState.NAME,
                field("value", value),
                field("state", state),
                field("trace", trace));
    }

    static <A> Term<A> flowStateValue() {
        return projection(FlowState.NAME, "value");
    }

    static <A> Term<A> flowStateState() {
        return projection(FlowState.NAME, "state");
    }

    static <A> Term<A> flowStateTrace() {
        return projection(FlowState.NAME, "trace");
    }

    static <A> Term<A> foldOpt(OptionalCases<A> cases) {
        return elimination(new Elimination.Optional<>(cases));
    }

    static <A> Term<A> function(final Function<A> fun) {
        return new Term.Function<>(fun);
    }

    static <A> Term<A> int8(final short value) {
        return literal(Literals.int8(value));
    }

    static <A> Term<A> int16(final short value) {
        return literal(Literals.int16(value));
    }

    static <A> Term<A> int32(final int value) {
        return literal(Literals.int32(value));
    }

    static <A> Term<A> int64(final long value) {
        return literal(Literals.int64(value));
    }

    static <A> Term<A> integer(final IntegerValue value) {
        return literal(Literals.integer(value));
    }

    static <A> Term<A> just(final Term<A> elem) {
        return optional(Optional.of(elem));
    }

    static <A> Term<A> just(final String elem) {
        return just(variable(elem));
    }

    static <A> Term<A> lambda(final String var, final Term<A> body) {
        return function(new Function.Lambda<>(new Lambda<>(new Name(var), body)));
    }

    static <A> Term<A> lambda(final String var1, final String var2, final Term<A> body) {
        return lambda(var1, lambda(var2, body));
    }

    static <A> Term<A> lambda(final String var1, final String var2, final String var3, final Term<A> body) {
        return lambda(var1, lambda(var2, lambda(var3, body)));
    }

    static <A> Term<A> let(final String var, final Term<A> defined, final Term<A> definedIn) {
        Map<Name, Term<A>> bindings = new HashMap<>();
        bindings.put(new Name(var), defined);
        return new Term.Let<>(new Let<>(bindings, definedIn));
    }

    static <A> Term<A> list(final List<Term<A>> elements) {
        return new Term.List<>(elements);
    }

    static <A> Term<A> list(final Term<A>... elements) {
        return list(Arrays.asList(elements));
    }

    static <A> Term<A> listOfStrings(final List<String> elements) {
        List<Term<A>> terms = new ArrayList<>();
        for (String s : elements) {
            terms.add(string(s));
        }
        return list(terms);
    }

    static <A> Term<A> literal(final Literal value) {
        return new Term.Literal<>(value);
    }

    static <A> Term<A> map(final Map<Term<A>, Term<A>> value) {
        return new Term.Map<>(value);
    }

    static <A> Term<A> match(final Name name, final Optional<Term<A>> def,
                             final Map.Entry<String, Term<A>>... casePairs) {
        Field<A>[] fields = new Field[casePairs.length];
        for (int i = 0; i < casePairs.length; i++) {
            fields[i] = field(casePairs[i].getKey(), casePairs[i].getValue());
        }
        return cases(name, def, fields);
    }

    static <A> Term<A> nothing() {
        return optional(Optional.empty());
    }

    static <A> Term<A> optional(final Optional<Term<A>> maybeTerm) {
        return new Term.Optional<>(maybeTerm);
    }

    static <A> Term<A> pair(final Term<A> left, final Term<A> right) {
        return new Term.Product<>(Arrays.asList(left, right));
    }

    static <A> Term<A> pair(final Tuple.Tuple2<Term<A>, Term<A>> tuple) {
        return pair(tuple.object1, tuple.object2);
    }

    static <A> Term<A> primitive(final Name primName) {
        return function(new Function.Primitive<>(primName));
    }

    static <A> Term<A> primitive(final String primName) {
        return primitive(name(primName));
    }

    static <A> Term<A> projection(final Name recordName, final Name fname) {
        return elimination(new Elimination.Record<>(new Projection(recordName, fname)));
    }

    static <A> Term<A> projection(final String recordName, final String fname) {
        return projection(name(recordName), new Name(fname));
    }

    static <A> Term<A> projection(final Name recordName, final String fname) {
        return projection(recordName, new Name(fname));
    }

    static <A> Term<A> record(final Name recordName, final Field<A>... fields) {
        return new Term.Record<>(new Record<>(recordName, Arrays.asList(fields)));
    }

    static <A> Term<A> record(final String recordName, final Field<A>... fields) {
        return record(name(recordName), fields);
    }

    static <A> Term<A> set(final Set<Term<A>> value) {
        return new Term.Set<>(value);
    }

    static <A> Term<A> string(final String value) {
        return literal(Literals.string(value));
    }

    static <A> Term<A> uint8(final byte value) {
        return literal(Literals.uint8(value));
    }

    static <A> Term<A> uint16(final char value) {
        return literal(Literals.uint16(value));
    }

    static <A> Term<A> uint32(final long value) {
        return literal(Literals.uint32(value));
    }

    static <A> Term<A> uint64(final BigInteger value) {
        return literal(Literals.uint64(value));
    }

    static <A> Term<A> inject(final Name unionName, final Field<A> field) {
        return new Term.Union<>(new Injection<>(unionName, field));
    }

    static <A> Term<A> inject(final String unionName, final Field<A> field) {
        return inject(name(unionName), field);
    }

    static <A> Term<A> unit() {
        return record(UnitType.NAME);
    }

    static <A> Term<A> unwrap(final Name name) {
        return elimination(new Elimination.Wrap<>(name));
    }

    static <A> Term<A> variable(final String var) {
        return new Term.Variable<>(new Name(var));
    }

    static <A> Term<A> wrap(final Name name, final Term<A> term) {
        return new Term.Wrap<>(new Nominal<>(name, term));
    }
}
