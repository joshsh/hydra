package hydra.dsl;

import hydra.core.Annotated;
import hydra.core.Application;
import hydra.core.CaseStatement;
import hydra.core.Elimination;
import hydra.core.Field;
import hydra.core.FieldName;
import hydra.core.FloatValue;
import hydra.core.Function;
import hydra.core.Injection;
import hydra.core.IntegerValue;
import hydra.core.Lambda;
import hydra.core.Let;
import hydra.core.Literal;
import hydra.core.Name;
import hydra.core.Projection;
import hydra.core.Record;
import hydra.core.Term;
import hydra.core.UnitType;

import hydra.core.Nominal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static hydra.dsl.Core.*;


public interface Terms {
  static <A> Term<A> annot(final A ann, final Term<A> base) {
    return new Term.Annotated<>(new Annotated<>(base, ann));
  }

  static <A> Term<A> apply(final Term<A> lhs, final Term<A> rhs) {
    return new Term.Application<>(new Application<>(lhs, rhs));
  }

  static <A> Term<A> bigfloat(final double value) {
    return float_(new FloatValue.Bigfloat(value));
  }

  static <A> Term<A> bigint(final BigInteger value) {
    return integer(new IntegerValue.Bigint(value));
  }

  static <A> Term<A> binary(final String value) {
    return literal(new Literal.Binary(value));
  }

  static <A> Term<A> boolean_(final boolean value) {
    return literal(new Literal.Boolean_(value));
  }

  static <A> Term<A> cases(final Name name, final Optional<Term<A>> def, final Field<A>... fields) {
    return elimination(new Elimination.Union<>(new CaseStatement<>(name, def, Arrays.asList(fields))));
  }

  static <A> Term<A> delta() {
    return elimination(new Elimination.Element<>());
  }

  static <A> Term<A> elimination(final Elimination<A> elim) {
    return function(new Function.Elimination<>(elim));
  }

  static <A> Field<A> field(final String fname, final Term<A> term) {
    return new Field<>(new FieldName(fname), term);
  }

  static <A> Term<A> float_(final FloatValue value) {
    return literal(new Literal.Float_(value));
  }

  static <A> Term<A> float32(final float value) {
    return float_(new FloatValue.Float32(value));
  }

  static <A> Term<A> float64(final double value) {
    return float_(new FloatValue.Float64(value));
  }

  static <A> Term<A> function(final Function<A> fun) {
    return new Term.Function<>(fun);
  }

  static <A> Term<A> int8(final short value) {
    return integer(new IntegerValue.Int8(value));
  }

  static <A> Term<A> int16(final short value) {
    return integer(new IntegerValue.Int16(value));
  }

  static <A> Term<A> int32(final int value) {
    return integer(new IntegerValue.Int32(value));
  }

  static <A> Term<A> int64(final long value) {
    return integer(new IntegerValue.Int64(value));
  }

  static <A> Term<A> integer(final IntegerValue value) {
    return literal(new Literal.Integer_(value));
  }

  static <A> Term<A> lambda(final String var, final Term<A> body) {
    return function(new Function.Lambda<>(new Lambda<>(new Name(var), body)));
  }

  static <A> Term<A> let(final String var, final Term<A> defined, final Term<A> definedIn) {
    Map<Name, Term<A>> bindings = new HashMap<>();
    bindings.put(new Name(var), defined);
    return new Term.Let<>(new Let<>(bindings, definedIn));
  }

  static <A> Term<A> list(final Term<A>... elements) {
    return new Term.List<>(Arrays.asList(elements));
  }

  static <A> Term<A> literal(final Literal value) {
    return new Term.Literal<>(value);
  }

  static <A> Term<A> map(final Map<Term<A>, Term<A>> value) {
    return new Term.Map<>(value);
  }

  static <A> Term<A> match(final Name name, final Optional<Term<A>> def, final Map.Entry<String, Term<A>>... casePairs) {
    Field<A>[] fields = new Field[casePairs.length];
    for (int i = 0; i < casePairs.length; i++) {
      fields[i] = field(casePairs[i].getKey(), casePairs[i].getValue());
    }
    return cases(name, def, fields);
  }

  static <A> Term<A> optional(final Optional<Term<A>> maybeTerm) {
    return new Term.Optional<>(maybeTerm);
  }

  static <A> Term<A> primitive(final Name primName) {
    return function(new Function.Primitive<>(primName));
  }

  static <A> Term<A> primitive(final String primName) {
    return primitive(name(primName));
  }

  static <A> Term<A> projection(final Name recordName, final FieldName fname) {
    return elimination(new Elimination.Record<>(new Projection(recordName, fname)));
  }

  static <A> Term<A> projection(final String recordName, final String fname) {
    return projection(name(recordName), new FieldName(fname));
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
    return literal(new Literal.String_(value));
  }

  static <A> Term<A> uint8(final byte value) {
    return integer(new IntegerValue.Uint8(value));
  }

  static <A> Term<A> uint16(final char value) {
    return integer(new IntegerValue.Uint16(value));
  }

  static <A> Term<A> uint32(final long value) {
    return integer(new IntegerValue.Uint32(value));
  }

  static <A> Term<A> uint64(final BigInteger value) {
    return integer(new IntegerValue.Uint64(value));
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

  static <A> Term<A> variable(final String var) {
    return new Term.Variable<>(new Name(var));
  }

  static <A> Term<A> wrap(final Name name, final Term<A> term) {
    return new Term.Wrap<>(new Nominal<>(name, term));
  }
}
