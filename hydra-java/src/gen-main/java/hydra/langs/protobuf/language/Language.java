package hydra.langs.protobuf.language;

public interface Language {
  static <A> hydra.coders.Language<A> protobufLanguage() {
    return new hydra.coders.Language(new hydra.coders.LanguageName("hydra/langs/protobuf"), new hydra.coders.LanguageConstraints(hydra.lib.sets.Empty.apply(), hydra.lib.sets.FromList.apply(java.util.Arrays.asList(
      new hydra.mantle.LiteralVariant.Binary(),
      new hydra.mantle.LiteralVariant.Boolean_(),
      new hydra.mantle.LiteralVariant.Float_(),
      new hydra.mantle.LiteralVariant.Integer_(),
      new hydra.mantle.LiteralVariant.String_())), hydra.lib.sets.FromList.apply(java.util.Arrays.asList(
      new hydra.core.FloatType.Float32(),
      new hydra.core.FloatType.Float64())), hydra.lib.sets.Empty.apply(), hydra.lib.sets.FromList.apply(java.util.Arrays.asList(
      new hydra.core.IntegerType.Int32(),
      new hydra.core.IntegerType.Int64(),
      new hydra.core.IntegerType.Uint32(),
      new hydra.core.IntegerType.Uint64())), hydra.lib.sets.FromList.apply(java.util.Arrays.asList(
      new hydra.mantle.TermVariant.List(),
      new hydra.mantle.TermVariant.Literal(),
      new hydra.mantle.TermVariant.Map(),
      new hydra.mantle.TermVariant.Optional(),
      new hydra.mantle.TermVariant.Record(),
      new hydra.mantle.TermVariant.Union())), hydra.lib.sets.FromList.apply(java.util.Arrays.asList(
      new hydra.mantle.TypeVariant.Annotated(),
      new hydra.mantle.TypeVariant.List(),
      new hydra.mantle.TypeVariant.Literal(),
      new hydra.mantle.TypeVariant.Map(),
      new hydra.mantle.TypeVariant.Optional(),
      new hydra.mantle.TypeVariant.Record(),
      new hydra.mantle.TypeVariant.Union(),
      new hydra.mantle.TypeVariant.Variable())), (java.util.function.Function<hydra.core.Type<A>, Boolean>) (v1 -> ((v1)).accept(new hydra.core.Type.PartialVisitor<>() {
      @Override
      public Boolean otherwise(hydra.core.Type<A> instance) {
        return true;
      }
      
      @Override
      public Boolean visit(hydra.core.Type.Map<A> instance) {
        return (hydra.strip.Strip.stripType(((instance.value)).values)).accept(new hydra.core.Type.PartialVisitor<>() {
          @Override
          public Boolean otherwise(hydra.core.Type<A> instance) {
            return true;
          }
          
          @Override
          public Boolean visit(hydra.core.Type.Optional<A> instance) {
            return false;
          }
        });
      }
    }))));
  }
  
  static java.util.Set<String> protobufReservedWords() {
    java.util.List<String> fieldNames = java.util.Arrays.asList(
      "case",
      "class",
      "data",
      "default",
      "deriving",
      "do",
      "else",
      "foreign",
      "if",
      "import",
      "in",
      "infix",
      "infixl",
      "infixr",
      "instance",
      "let",
      "mdo",
      "module",
      "newtype",
      "of",
      "pattern",
      "proc",
      "rec",
      "then",
      "type",
      "where");
    return hydra.lib.sets.FromList.apply(hydra.lib.lists.Concat.apply(java.util.Arrays.asList((fieldNames))));
  }
}