package hydra.coreEncoding;

/**
 * Mapping of hydra/core constructs in a host language like Haskell or Java  to their native Hydra counterparts as terms.  This includes an implementation of LambdaGraph's epsilon encoding (types to terms).
 */
public interface CoreEncoding {
  static <A> hydra.core.Term<A> coreEncodeAnnotatedTerm(hydra.core.Annotated<hydra.core.Term<A>, A> a) {
    return new hydra.core.Term.Annotated(new hydra.core.Annotated(hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((a)).subject), ((a)).annotation));
  }
  
  static <A> hydra.core.Term<A> coreEncodeAnnotatedType(hydra.core.Annotated<hydra.core.Type<A>, A> at) {
    return new hydra.core.Term.Annotated(new hydra.core.Annotated(hydra.coreEncoding.CoreEncoding.coreEncodeType(((at)).subject), ((at)).annotation));
  }
  
  static <A> hydra.core.Term<A> coreEncodeApplication(hydra.core.Application<A> app) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Application"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("function"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((app)).function)),
      new hydra.core.Field(new hydra.core.Name("argument"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((app)).argument)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeApplicationType(hydra.core.ApplicationType<A> at) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.ApplicationType"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("function"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((at)).function)),
      new hydra.core.Field(new hydra.core.Name("argument"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((at)).argument)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeCaseStatement(hydra.core.CaseStatement<A> cs) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.CaseStatement"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("typeName"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((cs)).typeName)),
      new hydra.core.Field(new hydra.core.Name("default"), new hydra.core.Term.Optional(hydra.lib.optionals.Map.apply(
        (hydra.coreEncoding.CoreEncoding::coreEncodeTerm),
        ((cs)).default_))),
      new hydra.core.Field(new hydra.core.Name("cases"), new hydra.core.Term.List(hydra.lib.lists.Map.apply(
        (hydra.coreEncoding.CoreEncoding::coreEncodeField),
        ((cs)).cases))))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeElimination(hydra.core.Elimination<A> v1) {
    return ((v1)).accept(new hydra.core.Elimination.Visitor<A, hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.Elimination.List<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Elimination"), new hydra.core.Field(new hydra.core.Name("list"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Elimination.Optional<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Elimination"), new hydra.core.Field(new hydra.core.Name("optional"), hydra.coreEncoding.CoreEncoding.coreEncodeOptionalCases((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Elimination.Product<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Elimination"), new hydra.core.Field(new hydra.core.Name("product"), hydra.coreEncoding.CoreEncoding.coreEncodeTupleProjection((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Elimination.Record<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Elimination"), new hydra.core.Field(new hydra.core.Name("record"), hydra.coreEncoding.CoreEncoding.coreEncodeProjection((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Elimination.Union<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Elimination"), new hydra.core.Field(new hydra.core.Name("union"), hydra.coreEncoding.CoreEncoding.coreEncodeCaseStatement((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Elimination.Wrap<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Elimination"), new hydra.core.Field(new hydra.core.Name("wrap"), hydra.coreEncoding.CoreEncoding.coreEncodeName((instance.value)))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeField(hydra.core.Field<A> f) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Field"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("name"), new hydra.core.Term.Wrap(new hydra.core.Nominal(new hydra.core.Name("hydra.core.Name"), new hydra.core.Term.Literal(new hydra.core.Literal.String_((((f)).name).value))))),
      new hydra.core.Field(new hydra.core.Name("term"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((f)).term)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeFieldType(hydra.core.FieldType<A> ft) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.FieldType"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("name"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((ft)).name)),
      new hydra.core.Field(new hydra.core.Name("type"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((ft)).type)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeFloatType(hydra.core.FloatType v1) {
    return ((v1)).accept(new hydra.core.FloatType.Visitor<hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.FloatType.Bigfloat instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.FloatType"), new hydra.core.Field(new hydra.core.Name("bigfloat"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.FloatType.Float32 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.FloatType"), new hydra.core.Field(new hydra.core.Name("float32"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.FloatType.Float64 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.FloatType"), new hydra.core.Field(new hydra.core.Name("float64"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeFloatValue(hydra.core.FloatValue v1) {
    return ((v1)).accept(new hydra.core.FloatValue.Visitor<hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.FloatValue.Bigfloat instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.FloatValue"), new hydra.core.Field(new hydra.core.Name("bigfloat"), new hydra.core.Term.Literal(new hydra.core.Literal.Float_(new hydra.core.FloatValue.Bigfloat((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.FloatValue.Float32 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.FloatValue"), new hydra.core.Field(new hydra.core.Name("float32"), new hydra.core.Term.Literal(new hydra.core.Literal.Float_(new hydra.core.FloatValue.Float32((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.FloatValue.Float64 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.FloatValue"), new hydra.core.Field(new hydra.core.Name("float64"), new hydra.core.Term.Literal(new hydra.core.Literal.Float_(new hydra.core.FloatValue.Float64((instance.value)))))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeFunction(hydra.core.Function<A> v1) {
    return ((v1)).accept(new hydra.core.Function.Visitor<A, hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.Function.Elimination<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Function"), new hydra.core.Field(new hydra.core.Name("elimination"), hydra.coreEncoding.CoreEncoding.coreEncodeElimination((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Function.Lambda<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Function"), new hydra.core.Field(new hydra.core.Name("lambda"), hydra.coreEncoding.CoreEncoding.coreEncodeLambda((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Function.Primitive<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Function"), new hydra.core.Field(new hydra.core.Name("primitive"), hydra.coreEncoding.CoreEncoding.coreEncodeName((instance.value)))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeFunctionType(hydra.core.FunctionType<A> ft) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.FunctionType"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("domain"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((ft)).domain)),
      new hydra.core.Field(new hydra.core.Name("codomain"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((ft)).codomain)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeInjection(hydra.core.Injection<A> i) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Injection"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("typeName"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((i)).typeName)),
      new hydra.core.Field(new hydra.core.Name("field"), hydra.coreEncoding.CoreEncoding.coreEncodeField(((i)).field)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeIntegerType(hydra.core.IntegerType v1) {
    return ((v1)).accept(new hydra.core.IntegerType.Visitor<hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Bigint instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("bigint"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Int8 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("int8"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Int16 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("int16"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Int32 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("int32"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Int64 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("int64"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Uint8 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("uint8"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Uint16 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("uint16"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Uint32 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("uint32"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerType.Uint64 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerType"), new hydra.core.Field(new hydra.core.Name("uint64"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeIntegerValue(hydra.core.IntegerValue v1) {
    return ((v1)).accept(new hydra.core.IntegerValue.Visitor<hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Bigint instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("bigint"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Bigint((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Int8 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("int8"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int8((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Int16 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("int16"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int16((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Int32 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("int32"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Int64 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("int64"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int64((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Uint8 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("uint8"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Uint8((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Uint16 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("uint16"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Uint16((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Uint32 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("uint32"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Uint32((instance.value)))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.IntegerValue.Uint64 instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.IntegerValue"), new hydra.core.Field(new hydra.core.Name("uint64"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Uint64((instance.value)))))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeLambda(hydra.core.Lambda<A> l) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Lambda"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("parameter"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((l)).parameter)),
      new hydra.core.Field(new hydra.core.Name("body"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((l)).body)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeLambdaType(hydra.core.LambdaType<A> lt) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.LambdaType"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("parameter"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((lt)).parameter)),
      new hydra.core.Field(new hydra.core.Name("body"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((lt)).body)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeLiteral(hydra.core.Literal v1) {
    return ((v1)).accept(new hydra.core.Literal.Visitor<hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.Literal.Binary instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Literal"), new hydra.core.Field(new hydra.core.Name("binary"), new hydra.core.Term.Literal(new hydra.core.Literal.Binary((instance.value))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Literal.Boolean_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Literal"), new hydra.core.Field(new hydra.core.Name("boolean"), new hydra.core.Term.Literal(new hydra.core.Literal.Boolean_((instance.value))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Literal.Float_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Literal"), new hydra.core.Field(new hydra.core.Name("float"), hydra.coreEncoding.CoreEncoding.coreEncodeFloatValue((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Literal.Integer_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Literal"), new hydra.core.Field(new hydra.core.Name("integer"), hydra.coreEncoding.CoreEncoding.coreEncodeIntegerValue((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Literal.String_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Literal"), new hydra.core.Field(new hydra.core.Name("string"), new hydra.core.Term.Literal(new hydra.core.Literal.String_((instance.value))))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeLiteralType(hydra.core.LiteralType v1) {
    return ((v1)).accept(new hydra.core.LiteralType.Visitor<hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.LiteralType.Binary instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.LiteralType"), new hydra.core.Field(new hydra.core.Name("binary"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.LiteralType.Boolean_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.LiteralType"), new hydra.core.Field(new hydra.core.Name("boolean"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.LiteralType.Float_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.LiteralType"), new hydra.core.Field(new hydra.core.Name("float"), hydra.coreEncoding.CoreEncoding.coreEncodeFloatType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.LiteralType.Integer_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.LiteralType"), new hydra.core.Field(new hydra.core.Name("integer"), hydra.coreEncoding.CoreEncoding.coreEncodeIntegerType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.LiteralType.String_ instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.LiteralType"), new hydra.core.Field(new hydra.core.Name("string"), new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.UnitType"), java.util.Arrays.asList())))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeMapType(hydra.core.MapType<A> mt) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.MapType"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("keys"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((mt)).keys)),
      new hydra.core.Field(new hydra.core.Name("values"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((mt)).values)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeName(hydra.core.Name fn) {
    return new hydra.core.Term.Wrap(new hydra.core.Nominal(new hydra.core.Name("hydra/core.Name"), new hydra.core.Term.Literal(new hydra.core.Literal.String_(((fn)).value))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeNominalTerm(hydra.core.Nominal<hydra.core.Term<A>> n) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Nominal"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("typeName"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((n)).typeName)),
      new hydra.core.Field(new hydra.core.Name("object"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((n)).object)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeNominalType(hydra.core.Nominal<hydra.core.Type<A>> nt) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Nominal"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("typeName"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((nt)).typeName)),
      new hydra.core.Field(new hydra.core.Name("object"), hydra.coreEncoding.CoreEncoding.coreEncodeType(((nt)).object)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeOptionalCases(hydra.core.OptionalCases<A> oc) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.OptionalCases"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("nothing"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((oc)).nothing)),
      new hydra.core.Field(new hydra.core.Name("just"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((oc)).just)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeProjection(hydra.core.Projection p) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Projection"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("typeName"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((p)).typeName)),
      new hydra.core.Field(new hydra.core.Name("field"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((p)).field)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeRecord(hydra.core.Record<A> r) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Record"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("typeName"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((r)).typeName)),
      new hydra.core.Field(new hydra.core.Name("fields"), new hydra.core.Term.List(hydra.lib.lists.Map.apply(
        (hydra.coreEncoding.CoreEncoding::coreEncodeField),
        ((r)).fields))))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeRowType(hydra.core.RowType<A> rt) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.RowType"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("typeName"), hydra.coreEncoding.CoreEncoding.coreEncodeName(((rt)).typeName)),
      new hydra.core.Field(new hydra.core.Name("extends"), new hydra.core.Term.Optional(hydra.lib.optionals.Map.apply(
        (hydra.coreEncoding.CoreEncoding::coreEncodeName),
        ((rt)).extends_))),
      new hydra.core.Field(new hydra.core.Name("fields"), new hydra.core.Term.List(hydra.lib.lists.Map.apply(
        (hydra.coreEncoding.CoreEncoding::coreEncodeFieldType),
        ((rt)).fields))))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeSum(hydra.core.Sum<A> s) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.Sum"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("index"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(((s)).index)))),
      new hydra.core.Field(new hydra.core.Name("size"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(((s)).size)))),
      new hydra.core.Field(new hydra.core.Name("term"), hydra.coreEncoding.CoreEncoding.coreEncodeTerm(((s)).term)))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeTerm(hydra.core.Term<A> v1) {
    return ((v1)).accept(new hydra.core.Term.PartialVisitor<A, hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> otherwise(hydra.core.Term<A> instance) {
        return new hydra.core.Term.Literal(new hydra.core.Literal.String_("not implemented"));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Annotated<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("annotated"), hydra.coreEncoding.CoreEncoding.coreEncodeAnnotatedTerm((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Application<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("application"), hydra.coreEncoding.CoreEncoding.coreEncodeApplication((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Function<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("function"), hydra.coreEncoding.CoreEncoding.coreEncodeFunction((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Literal<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("literal"), hydra.coreEncoding.CoreEncoding.coreEncodeLiteral((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.List<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("list"), new hydra.core.Term.List(hydra.lib.lists.Map.apply(
          (hydra.coreEncoding.CoreEncoding::coreEncodeTerm),
          (instance.value))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Optional<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("optional"), new hydra.core.Term.Optional(hydra.lib.optionals.Map.apply(
          (hydra.coreEncoding.CoreEncoding::coreEncodeTerm),
          (instance.value))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Product<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("product"), new hydra.core.Term.List(hydra.lib.lists.Map.apply(
          (hydra.coreEncoding.CoreEncoding::coreEncodeTerm),
          (instance.value))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Record<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("record"), hydra.coreEncoding.CoreEncoding.coreEncodeRecord((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Sum<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("sum"), hydra.coreEncoding.CoreEncoding.coreEncodeSum((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Union<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("union"), hydra.coreEncoding.CoreEncoding.coreEncodeInjection((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Variable<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("variable"), hydra.coreEncoding.CoreEncoding.coreEncodeName((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Term.Wrap<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Term"), new hydra.core.Field(new hydra.core.Name("wrap"), hydra.coreEncoding.CoreEncoding.coreEncodeNominalTerm((instance.value)))));
      }
    });
  }
  
  static <A> hydra.core.Term<A> coreEncodeTupleProjection(hydra.core.TupleProjection tp) {
    return new hydra.core.Term.Record(new hydra.core.Record(new hydra.core.Name("hydra/core.TupleProjection"), java.util.Arrays.asList(
      new hydra.core.Field(new hydra.core.Name("arity"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(((tp)).arity)))),
      new hydra.core.Field(new hydra.core.Name("index"), new hydra.core.Term.Literal(new hydra.core.Literal.Integer_(new hydra.core.IntegerValue.Int32(((tp)).index)))))));
  }
  
  static <A> hydra.core.Term<A> coreEncodeType(hydra.core.Type<A> v1) {
    return ((v1)).accept(new hydra.core.Type.Visitor<A, hydra.core.Term<A>>() {
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Annotated<A> instance) {
        return new hydra.core.Term.Annotated(new hydra.core.Annotated(hydra.coreEncoding.CoreEncoding.coreEncodeType(((instance.value)).subject), ((instance.value)).annotation));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Application<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("application"), hydra.coreEncoding.CoreEncoding.coreEncodeApplicationType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Function<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("function"), hydra.coreEncoding.CoreEncoding.coreEncodeFunctionType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Lambda<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("lambda"), hydra.coreEncoding.CoreEncoding.coreEncodeLambdaType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.List<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("list"), hydra.coreEncoding.CoreEncoding.coreEncodeType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Literal<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("literal"), hydra.coreEncoding.CoreEncoding.coreEncodeLiteralType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Map<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("map"), hydra.coreEncoding.CoreEncoding.coreEncodeMapType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Optional<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("optional"), hydra.coreEncoding.CoreEncoding.coreEncodeType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Product<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("product"), new hydra.core.Term.List(hydra.lib.lists.Map.apply(
          (hydra.coreEncoding.CoreEncoding::coreEncodeType),
          (instance.value))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Record<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("record"), hydra.coreEncoding.CoreEncoding.coreEncodeRowType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Set<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("set"), hydra.coreEncoding.CoreEncoding.coreEncodeType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Stream<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("stream"), hydra.coreEncoding.CoreEncoding.coreEncodeType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Sum<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("sum"), new hydra.core.Term.List(hydra.lib.lists.Map.apply(
          (hydra.coreEncoding.CoreEncoding::coreEncodeType),
          (instance.value))))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Union<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("union"), hydra.coreEncoding.CoreEncoding.coreEncodeRowType((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Variable<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("variable"), hydra.coreEncoding.CoreEncoding.coreEncodeName((instance.value)))));
      }
      
      @Override
      public hydra.core.Term<A> visit(hydra.core.Type.Wrap<A> instance) {
        return new hydra.core.Term.Union(new hydra.core.Injection(new hydra.core.Name("hydra/core.Type"), new hydra.core.Field(new hydra.core.Name("wrap"), hydra.coreEncoding.CoreEncoding.coreEncodeNominalType((instance.value)))));
      }
    });
  }
}
