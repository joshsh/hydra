package hydra.dsl;

import hydra.compute.Flow;
import hydra.core.AnnotatedType;
import hydra.core.ApplicationType;
import hydra.core.FieldType;
import hydra.core.FloatType;
import hydra.core.FunctionType;
import hydra.core.IntegerType;
import hydra.core.LambdaType;
import hydra.core.LiteralType;
import hydra.core.MapType;
import hydra.core.Name;
import hydra.core.RowType;
import hydra.core.Term;
import hydra.core.Type;
import hydra.core.TypeScheme;
import hydra.core.Unit;
import hydra.core.WrappedType;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static hydra.dsl.Core.name;


/**
 * A domain-specific language for constructing Hydra types in Java.
 */
public interface Types {
    Name PLACEHOLDER_NAME = name("Placeholder");

    /**
     * Construct an annotated type.
     */
    static Type annot(final Map<Name, Term> ann, final Type base) {
        return new Type.Annotated(new AnnotatedType(base, ann));
    }

    /**
     * Construct an annotation type with a single key/value pair.
     */
    static Type annot(final Name key, final Term value, final Type base) {
        Map<Name, Term> mp = new HashMap<>();
        mp.put(key, value);
        return annot(mp, base);
    }

    /**
     * Construct an application type.
     */
    static Type apply(final Type lhs, final Type... rhs) {
        Type cur = lhs;
        for (Type r : rhs) {
            cur = new Type.Application(new ApplicationType(cur, r));
        }
        return cur;
    }

    /**
     * Construct the bigfloat literal type.
     */
    static Type bigfloat() {
        return literal(LiteralTypes.bigfloat());
    }

    /**
     * Construct the bigint literal type.
     */
    static Type bigint() {
        return literal(LiteralTypes.bigint());
    }

    /**
     * Construct the binary literal type.
     */
    static Type binary() {
        return literal(LiteralTypes.binary());
    }

    /**
     * Construct the boolean literal type.
     */
    static Type boolean_() {
        return literal(LiteralTypes.boolean_());
    }

    /**
     * Construct an enumerated type.
     */
    static Type enum_(final String... names) {
        FieldType[] fields = new FieldType[names.length];
        for (int i = 0; i < names.length; i++) {
            fields[i] = field(names[i], unit());
        }

        return union(fields);
    }

    /**
     * Construct a field type.
     */
    static FieldType field(final String name, final Type t) {
        return new FieldType(new Name(name), t);
    }

    /**
     * Construct the float32 literal type.
     */
    static Type float32() {
        return literal(LiteralTypes.float32());
    }

    /**
     * Construct the float64 literal type.
     */
    static Type float64() {
        return literal(LiteralTypes.float64());
    }

    /**
     * Construct a float literal type.
     */
    static Type float_(final FloatType ftype) {
        return literal(LiteralTypes.float_(ftype));
    }

    /**
     * Construct a flow type.
     */
    static Type flow(final Type states, final Type elements) {
        return apply(variable(Flow.TYPE_NAME), states, elements);
    }

    /**
     * Construct a flow type.
     */
    static Type flow(final Type states, final String elements) {
        return apply(variable(Flow.TYPE_NAME), states, variable(elements));
    }

    /**
     * Construct a flow type.
     */
    static Type flow(final String states, final Type elements) {
        return apply(variable(Flow.TYPE_NAME), variable(states), elements);
    }

    /**
     * Construct a flow type.
     */
    static Type flow(final String states, final String elements) {
        return flow(variable(states), variable(elements));
    }

    /**
     * Construct a function type.
     */
    static Type function(final Type dom, final Type cod, final Type... more) {
        Type c;

        if (more.length == 0) {
            c = cod;
        } else {
            c = more[more.length - 1];
            for (int i = more.length - 2; i >= 0; i--) {
                c = new Type.Function(new FunctionType(more[i], c));
            }
            c = new Type.Function(new FunctionType(cod, c));
        }

        return new Type.Function(new FunctionType(dom, c));
    }

    /**
     * Construct a function type.
     */
    static Type function(final String dom, final Type cod, final Type... more) {
        return function(variable(dom), cod, more);
    }

    /**
     * Construct a function type.
     */
    static Type function(final Type dom, final String cod, final Type... more) {
        return function(dom, variable(cod), more);
    }

    /**
     * Construct a function type.
     */
    static Type function(final String dom, final String cod, final Type... more) {
        return function(variable(dom), variable(cod), more);
    }

    /**
     * Construct a function type.
     */
    static Type function(final String dom1, final String dom2, final String dom3, final Type... cod) {
        return function(variable(dom1), function(variable(dom2), variable(dom3), cod));
    }

    /**
     * Construct the int16 literal type.
     */
    static Type int16() {
        return literal(LiteralTypes.int16());
    }

    /**
     * Construct the int32 literal type.
     */
    static Type int32() {
        return literal(LiteralTypes.int32());
    }

    /**
     * Construct the int64 literal type.
     */
    static Type int64() {
        return literal(LiteralTypes.int64());
    }

    /**
     * Construct the int8 literal type.
     */
    static Type int8() {
        return literal(LiteralTypes.int8());
    }

    /**
     * Construct an integer type.
     */
    static Type integer(final IntegerType itype) {
        return literal(LiteralTypes.integer(itype));
    }

    /**
     * Construct a lambda (universal) type.
     */
    static Type lambda(final String var, final Type body) {
        return new Type.Lambda(new LambdaType(new Name(var), body));
    }

    /**
     * Construct a lambda (universal) type.
     */
    static Type lambda(final String var1, final String var2, final Type body) {
        return lambda(var1, lambda(var2, body));
    }

    /**
     * Construct a lambda (universal) type.
     */
    static Type lambda(final String var1, final String var2, final String var3, final Type body) {
        return lambda(var1, lambda(var2, lambda(var3, body)));
    }

    /**
     * Construct a list type.
     */
    static Type list(final Type elements) {
        return new Type.List(elements);
    }

    /**
     * Construct a list type.
     */
    static Type list(final String elements) {
        return new Type.List(variable(elements));
    }

    /**
     * Construct a literal type.
     */
    static Type literal(final LiteralType ltype) {
        return new Type.Literal(ltype);
    }

    /**
     * Construct a map type.
     */
    static Type map(final Type keys, final Type values) {
        return new Type.Map(new MapType(keys, values));
    }

    /**
     * Construct a map type.
     */
    static Type map(final String keys, final String values) {
        return map(variable(keys), variable(values));
    }

    /**
     * Construct an optional type.
     */
    static Type optional(final Type elements) {
        return new Type.Optional(elements);
    }

    /**
     * Construct an optional type.
     */
    static Type optional(final String elements) {
        return optional(variable(elements));
    }

    /**
     * Construct a pair type.
     */
    static Type pair(final Type fst, final Type snd) {
        List<Type> types = new ArrayList<>();
        types.add(fst);
        types.add(snd);
        return new Type.Product(types);
    }

    /**
     * Construct a record type.
     */
    static Type record(final FieldType... fields) {
        return record(PLACEHOLDER_NAME, fields);
    }

    /**
     * Construct a record type.
     */
    static Type record(final Name name, final FieldType... fields) {
        return new Type.Record(row(name, fields));
    }

    /**
     * Construct a record type.
     */
    static Type record(final String name, final FieldType... fields) {
        return record(name(name), fields);
    }

    /**
     * Construct a row type.
     */
    static RowType row(final Name name, final FieldType... fields) {
        return new RowType(name, Arrays.asList(fields));
    }

    /**
     * Construct a type scheme with no type variable
     */
    static TypeScheme scheme(final Type body) {
        return new TypeScheme(Collections.emptyList(), body);
    }

    /**
     * Construct a type scheme with one type variable
     */
    static TypeScheme scheme(final String var1, final Type body) {
        return new TypeScheme(Collections.singletonList(new Name(var1)), body);
    }

    /**
     * Construct a type scheme with two type variables
     */
    static TypeScheme scheme(final String var1, String var2, final Type body) {
        return new TypeScheme(Arrays.asList(new Name(var1), new Name(var2)), body);
    }

    /**
     * Construct a type scheme with three type variables
     */
    static TypeScheme scheme(final String var1, String var2, String var3, final Type body) {
        return new TypeScheme(Arrays.asList(new Name(var1), new Name(var2), new Name(var3)), body);
    }

    /**
     * Construct a set type.
     */
    static Type set(final Type elements) {
        return new Type.Set(elements);
    }

    /**
     * Construct a set type.
     */
    static Type set(final String elements) {
        return set(variable(elements));
    }

    /**
     * Construct the string literal type.
     */
    static Type string() {
        return literal(LiteralTypes.string());
    }

    /**
     * Construct a union type.
     */
    static Type union(final FieldType... fields) {
        return union(PLACEHOLDER_NAME, fields);
    }

    /**
     * Construct a union type.
     */
    static Type union(final Name name, final FieldType... fields) {
        return new Type.Union(row(name, fields));
    }

    /**
     * Construct a union type.
     */
    static Type union(final String name, final FieldType... fields) {
        return union(name(name), fields);
    }

    /**
     * Construct the uint16 literal type.
     */
    static Type uint16() {
        return literal(LiteralTypes.uint16());
    }

    /**
     * Construct the uint32 literal type.
     */
    static Type uint32() {
        return literal(LiteralTypes.uint32());
    }

    /**
     * Construct the uint64 literal type.
     */
    static Type uint64() {
        return literal(LiteralTypes.uint64());
    }

    /**
     * Construct the uint8 literal type.
     */
    static Type uint8() {
        return literal(LiteralTypes.uint8());
    }

    /**
     * Construct the unit type.
     */
    static Type unit() {
        return record(Unit.TYPE_NAME);
    }

    /**
     * Construct a type variable.
     */
    static Type variable(final Name name) {
        return new Type.Variable(name);
    }

    /**
     * Construct a type variable.
     */
    static Type variable(final String name) {
        return variable(new Name(name));
    }

    /**
     * Construct a wrapper type.
     */
    static Type wrap(final Name name, final Type type) {
        return new Type.Wrap(new WrappedType(name, type));
    }

    /**
     * Construct a wrapper type.
     */
    static Type wrap(final String name, final Type type) {
        return wrap(name(name), type);
    }
}
