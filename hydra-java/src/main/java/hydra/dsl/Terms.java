package hydra.dsl;

import hydra.compute.FlowState;
import hydra.core.AnnotatedTerm;
import hydra.core.Application;
import hydra.core.CaseStatement;
import hydra.core.Elimination;
import hydra.core.Field;
import hydra.core.FloatValue;
import hydra.core.Function;
import hydra.core.Injection;
import hydra.core.IntegerValue;
import hydra.core.Lambda;
import hydra.core.Let;
import hydra.core.LetBinding;
import hydra.core.Literal;
import hydra.core.Name;
import hydra.core.OptionalCases;
import hydra.core.Projection;
import hydra.core.Record;
import hydra.core.Term;
import hydra.core.Unit;
import hydra.core.WrappedTerm;
import hydra.util.Opt;
import hydra.util.Tuple;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static hydra.dsl.Core.*;


/**
 * A domain-specific language for constructing Hydra terms in Java.
 */
public interface Terms {
    /**
     * Construct an annotation term.
     */
    static Term annot(final Map<Name, Term> ann, final Term base) {
        return new Term.Annotated(new AnnotatedTerm(base, ann));
    }

    /**
     * Construct an annotation term with a single key/value pair.
     */
    static Term annot(final Name key, final Term value, final Term base) {
        Map<Name, Term> mp = new HashMap<>();
        mp.put(key, value);
        return annot(mp, base);
    }

    /**
     * Construct an annotation term with "description" annotation.
     */
    static Term annot(final String description, final Term base) {
        return annot(new Name("description"), Terms.string(description), base);
    }

    /**
     * Construct a compound application term.
     */
    static Term apply(final Term lhs, final Term... rhs) {
        Term cur = lhs;
        for (Term r : rhs) {
            cur = new Term.Application(new Application(lhs, r));
        }
        return cur;
    }

    /**
     * Construct an application term.
     */
    static Term app(final Term lhs, final Term... rhs) {
        return apply(lhs, rhs);
    }

    /**
     * Construct an application term.
     */
    static Term app(final String lhs, final Term... rhs) {
        return apply(variable(lhs), rhs);
    }

    /**
     * Construct an application term.
     */
    static Term app(final String lhs, final String rhs) {
        return app(lhs, variable(rhs));
    }

    /**
     * Construct an application term.
     */
    static Term app(final String lhs, final String rhs1, final String rhs2) {
        return app(lhs, variable(rhs1), variable(rhs2));
    }

    /**
     * Construct a bigfloat literal term.
     */
    static Term bigfloat(final double value) {
        return literal(Literals.bigfloat(value));
    }

    /**
     * Construct a bigint literal term.
     */
    static Term bigint(final BigInteger value) {
        return literal(Literals.bigint(value));
    }

    /**
     * Construct a binary literal term.
     */
    static Term binary(final String value) {
        return literal(Literals.binary(value));
    }

    /**
     * Construct a boolean literal term.
     */
    static Term boolean_(final boolean value) {
        return literal(Literals.boolean_(value));
    }

    /**
     * Construct a case (pattern-matching) term.
     */
    static Term cases(final Name name, final Opt<Term> def, final Field... fields) {
        return elimination(new Elimination.Union(new CaseStatement(name, def, Arrays.asList(fields))));
    }

    /**
     * Construct an elimination term.
     */
    static Term elimination(final Elimination elim) {
        return function(new Function.Elimination(elim));
    }

    /**
     * Construct a field.
     */
    static Field field(final String fname, final Term term) {
        return new Field(new Name(fname), term);
    }

    /**
     * Construct a field.
     */
    static Field field(final String fname, final String term) {
        return field(fname, variable(term));
    }

    /**
     * Construct a float literal term.
     */
    static Term float_(final FloatValue value) {
        return literal(Literals.float_(value));
    }

    /**
     * Construct a float32 literal term.
     */
    static Term float32(final float value) {
        return literal(Literals.float32(value));
    }

    /**
     * Construct a float64 literal term.
     */
    static Term float64(final double value) {
        return literal(Literals.float64(value));
    }

    /**
     * Construct a flow state term (used with the Flow monad).
     */
    static Term flowState(Term value, Term state, Term trace) {
        return record(FlowState.TYPE_NAME,
                field("value", value),
                field("state", state),
                field("trace", trace));
    }

    /**
     * Construct a value term (used with the Flow monad).
     */
    static Term flowStateValue() {
        return project(FlowState.TYPE_NAME, "value");
    }

    /**
     * Construct a state term (used with the Flow monad).
     */
    static Term flowStateState() {
        return project(FlowState.TYPE_NAME, "state");
    }

    /**
     * Construct a trace term (used with the Flow monad).
     */
    static Term flowStateTrace() {
        return project(FlowState.TYPE_NAME, "trace");
    }

    /**
     * Construct a fold term.
     */
    static Term fold(final Term fun) {
        return elimination(new Elimination.List(fun));
    }

    /**
     * Construct an optional-fold term.
     */
    static Term foldOpt(OptionalCases cases) {
        return elimination(new Elimination.Optional(cases));
    }

    /**
     * Construct a function term.
     */
    static Term function(final Function fun) {
        return new Term.Function(fun);
    }

    /**
     * Construct an int8 literal term.
     */
    static Term int8(final byte value) {
        return literal(Literals.int8(value));
    }

    /**
     * Construct an int16 literal term.
     */
    static Term int16(final short value) {
        return literal(Literals.int16(value));
    }

    /**
     * Construct an int32 literal term.
     */
    static Term int32(final int value) {
        return literal(Literals.int32(value));
    }

    /**
     * Construct an int64 literal term.
     */
    static Term int64(final long value) {
        return literal(Literals.int64(value));
    }

    /**
     * Construct an integer literal term.
     */
    static Term integer(final IntegerValue value) {
        return literal(Literals.integer(value));
    }

    /**
     * Construct a "just" (nonempty) term.
     */
    static Term just(final Term elem) {
        return optional(Opt.of(elem));
    }

    /**
     * Construct a "just" (nonempty) term.
     */
    static Term just(final String elem) {
        return just(variable(elem));
    }

    /**
     * Construct a lambda (anonymous function) term.
     */
    static Term lambda(final String var, final Term body) {
        return function(new Function.Lambda(new Lambda(new Name(var), Opt.empty(), body)));
    }

    /**
     * Construct a lambda (anonymous function) term.
     */
    static Term lambda(final String var1, final String var2, final Term body) {
        return lambda(var1, lambda(var2, body));
    }

    /**
     * Construct a lambda (anonymous function) term.
     */
    static Term lambda(final String var1, final String var2, final String var3, final Term body) {
        return lambda(var1, lambda(var2, lambda(var3, body)));
    }

    /**
     * Construct a 'let' term.
     */
    static Term let(final String var, final Term defined, final Term definedIn) {
        LetBinding b = new LetBinding(new Name(var), defined, Opt.empty());
        return new Term.Let(new Let(Collections.singletonList(b), definedIn));
    }

    /**
     * Construct a list term.
     */
    static Term list(final List<Term> elements) {
        return new Term.List(elements);
    }

    /**
     * Construct a list term.
     */
    static Term list(final Term... elements) {
        return list(Arrays.asList(elements));
    }

    /**
     * Construct a list of strings term.
     */
    static Term listOfStrings(final List<String> elements) {
        List<Term> terms = new ArrayList<>();
        for (String s : elements) {
            terms.add(string(s));
        }
        return list(terms);
    }

    /**
     * Construct a literal term.
     */
    static Term literal(final Literal value) {
        return new Term.Literal(value);
    }

    /**
     * Construct a map term.
     */
    static Term map(final Map<Term, Term> value) {
        return new Term.Map(value);
    }

    /**
     * Construct a match term.
     */
    static Term match(final Name name, final Opt<Term> def,
                      final Map.Entry<String, Term>... casePairs) {
        Field[] fields = new Field[casePairs.length];
        for (int i = 0; i < casePairs.length; i++) {
            fields[i] = field(casePairs[i].getKey(), casePairs[i].getValue());
        }
        return cases(name, def, fields);
    }

    /**
     * Construct a "nothing" (empty) term.
     */
    static Term nothing() {
        return optional(Opt.empty());
    }

    /**
     * Construct an optional term.
     */
    static Term optional(final Opt<Term> maybeTerm) {
        return new Term.Optional(maybeTerm);
    }

    /**
     * Construct a pair term.
     */
    static Term pair(final Term left, final Term right) {
        return new Term.Product(Arrays.asList(left, right));
    }

    /**
     * Construct a pair term.
     */
    static Term pair(final Tuple.Tuple2<Term, Term> tuple) {
        return pair(tuple.object1, tuple.object2);
    }

    /**
     * Construct a primitive function term.
     */
    static Term primitive(final Name primName) {
        return function(new Function.Primitive(primName));
    }

    /**
     * Construct a primitive function term.
     */
    static Term primitive(final String primName) {
        return primitive(name(primName));
    }

    /**
     * Construct a projection term.
     */
    static Term project(final Name recordName, final Name fname) {
        return elimination(new Elimination.Record(new Projection(recordName, fname)));
    }

    /**
     * Construct a projection term.
     */
    static Term project(final String recordName, final String fname) {
        return project(name(recordName), new Name(fname));
    }

    /**
     * Construct a projection term.
     */
    static Term project(final Name recordName, final String fname) {
        return project(recordName, new Name(fname));
    }

    /**
     * Construct a record term.
     */
    static Term record(final Name recordName, final Field... fields) {
        return new Term.Record(new Record(recordName, Arrays.asList(fields)));
    }

    /**
     * Construct a record term.
     */
    static Term record(final String recordName, final Field... fields) {
        return record(name(recordName), fields);
    }

    /**
     * Construct a set term.
     */
    static Term set(final Set<Term> value) {
        return new Term.Set(value);
    }

    /**
     * Construct a string literal term.
     */
    static Term string(final String value) {
        return literal(Literals.string(value));
    }

    /**
     * Construct a uint8 literal term.
     */
    static Term uint8(final char value) {
        return literal(Literals.uint8(value));
    }

    /**
     * Construct a uint16 literal term.
     */
    static Term uint16(final char value) {
        return literal(Literals.uint16(value));
    }

    /**
     * Construct a uint32 literal term.
     */
    static Term uint32(final long value) {
        return literal(Literals.uint32(value));
    }

    /**
     * Construct a uint64 literal term.
     */
    static Term uint64(final BigInteger value) {
        return literal(Literals.uint64(value));
    }

    /**
     * Construct an injection term.
     */
    static Term inject(final Name unionName, final Field field) {
        return new Term.Union(new Injection(unionName, field));
    }

    /**
     * Construct an injection term.
     */
    static Term inject(final String unionName, final Field field) {
        return inject(name(unionName), field);
    }

    /**
     * Construct a unit term.
     */
    static Term unit() {
        return record(Unit.TYPE_NAME);
    }

    /**
     * Construct an 'unwrap' term.
     */
    static Term unwrap(final Name name) {
        return elimination(new Elimination.Wrap(name));
    }

    /**
     * Construct a variable term.
     */
    static Term variable(final String var) {
        return new Term.Variable(new Name(var));
    }

    /**
     * Construct a wrapper term.
     */
    static Term wrap(final Name name, final Term term) {
        return new Term.Wrap(new WrappedTerm(name, term));
    }
}
