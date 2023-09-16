module Hydra.Sources.Tier4.Langs.Scala.Meta where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


scalaMetaModule :: Module
scalaMetaModule = Module ns elements [] $
    Just "A Scala syntax model based on Scalameta (https://scalameta.org)"
  where
    ns = Namespace "hydra/langs/scala/meta"
    def = datatype ns
    meta = typeref ns

    elements = [

      def "PredefString" --  See scala/Predef.scala
        string,

      def "ScalaSymbol" $ --  See scala/Symbol.scala
        record [
          "name">: string],

--  scala/meta/Trees.scala source below this line. Hydra type definitions inline

-- package scala.meta
--
-- import org.scalameta.invariants._
-- import scala.meta.classifiers._
-- import scala.meta.inputs._
-- import scala.meta.tokens._
-- import scala.meta.prettyprinters._
-- import scala.meta.internal.trees._
-- import scala.meta.internal.trees.Metadata.binaryCompatField
-- @root trait Tree extends InternalTree {
      def "Tree" $ --  Note: ignoring fields of Tree and InternalTree for now
        union [
          "ref">: meta "Ref",
          "stat">: meta "Stat",
          "type">: meta "Type",
          "bounds">: meta "Type.Bounds",
          "pat">: meta "Pat",
          "member">: meta "Member",
          "ctor">: meta "Ctor",
          "template">: meta "Template",
          "mod">: meta "Mod",
          "enumerator">: meta "Enumerator",
          "importer">: meta "Importer",
          "importee">: meta "Importee",
          "caseTree">: meta "CaseTree",
          "source">: meta "Source",
          "quasi">: meta "Quasi"],
--   def parent: Option[Tree]
--   def children: List[Tree]
--
--   def pos: Position
--   def tokens(implicit dialect: Dialect): Tokens
--
--   final override def canEqual(that: Any): Boolean = this eq that.asInstanceOf[AnyRef]
--   final override def equals(that: Any): Boolean = this eq that.asInstanceOf[AnyRef]
--   final override def hashCode: Int = System.identityHashCode(this)
--   final override def toString = scala.meta.internal.prettyprinters.TreeToString(this)
-- }
--
-- object Tree extends InternalTreeXtensions {
--   implicit def classifiable[T <: Tree]: Classifiable[T] = null
--   implicit def showStructure[T <: Tree]: Structure[T] =
--     scala.meta.internal.prettyprinters.TreeStructure.apply[T]
--   implicit def showSyntax[T <: Tree](implicit dialect: Dialect): Syntax[T] =
--     scala.meta.internal.prettyprinters.TreeSyntax.apply[T](dialect)
-- }
--
-- @branch trait Ref extends Tree
      def "Ref" $
        union [
          "name">: meta "Name",
          "init">: meta "Init"],
-- @branch trait Stat extends Tree
      def "Stat" $
        union [
          "term">: meta "Data",
          "decl">: meta "Decl",
          "defn">: meta "Defn",
          "importExport">: meta "ImportExportStat"],
--
-- @branch trait Name extends Ref { def value: String }
      def "Name" $
        union [
          "value">: string,
          "anonymous">: unit,
          "indeterminate">: meta "PredefString"],
-- object Name {
--   def apply(value: String): Name = if (value == "") Name.Anonymous() else Name.Indeterminate(value)
--   def unapply(name: Name): Option[String] = Some(name.value)
--   @ast class Anonymous() extends Name {
--     def value = ""
--     checkParent(ParentChecks.NameAnonymous)
--   }
--   @ast class Indeterminate(value: Predef.String @nonEmpty) extends Name
-- }
--
-- @branch trait Lit extends Data with Pat with Type {
      def "Lit" $
        union [
--   def value: Any
-- }
-- object Lit {
--   def unapply(arg: Lit): Option[Any] = Some(arg.value)
--   @ast class Null() extends Lit { def value: Any = null }
          "null">: unit,
--   @ast class Int(value: scala.Int) extends Lit
          "int">: int32,
--   // NOTE: Lit.Double/Float are strings to work the same across JS/JVM. Example:
--   // 1.4f.toString == "1.399999976158142" // in JS
--   // 1.4f.toString == "1.4"               // in JVM
--   // See https://www.scala-js.org/doc/semantics.html-- tostring-of-float-double-and-unit
--   @ast class Double(format: scala.Predef.String) extends Lit { val value = format.toDouble }
          "double">: float64,
--   object Double { def apply(double: scala.Double): Double = Lit.Double(double.toString) }
--   @ast class Float(format: scala.Predef.String) extends Lit { val value = format.toFloat }
          "float">: float32,
--   object Float { def apply(float: scala.Float): Float = Lit.Float(float.toString) }
--   @ast class Byte(value: scala.Byte) extends Lit
          "byte">: int8,
--   @ast class Short(value: scala.Short) extends Lit
          "short">: int16,
--   @ast class Char(value: scala.Char) extends Lit
          "char">: uint16,
--   @ast class Long(value: scala.Long) extends Lit
          "long">: int64,
--   @ast class Boolean(value: scala.Boolean) extends Lit
          "boolean">: boolean,
--   @ast class Unit() extends Lit { def value: Any = () }
          "unit">: unit,
--   @ast class String(value: scala.Predef.String) extends Lit
          "string">: string,
--   @ast class Symbol(value: scala.Symbol) extends Lit
          "symbol">: meta "ScalaSymbol"],
-- }
--
-- @branch trait Data extends Stat
      def "Data" $
        union [
          "lit">: meta "Lit",
          "ref">: meta "Data.Ref",
          "interpolate">: meta "Data.Interpolate",
          "xml">: meta "Data.Xml",
          "apply">: meta "Data.Apply",
          "applyUsing">: meta "Data.ApplyUsing",
          "applyType">: meta "Data.ApplyType",
          "assign">: meta "Data.Assign",
          "return">: meta "Data.Return",
          "throw">: meta "Data.Throw",
          "ascribe">: meta "Data.Ascribe",
          "annotate">: meta "Data.Annotate",
          "tuple">: meta "Data.Tuple",
          "block">: meta "Data.Block",
          "endMarker">: meta "Data.EndMarker",
          "if">: meta "Data.If",
          "quotedMacroExpr">: meta "Data.QuotedMacroExpr",
          "quotedMacroType">: meta "Data.QuotedMacroType",
          "splicedMacroExpr">: meta "Data.SplicedMacroExpr",
          "match">: meta "Data.Match",
          "try">: meta "Data.Try",
          "tryWithHandler">: meta "Data.TryWithHandler",
          "functionData">: meta "Data.FunctionData",
          "polyFunction">: meta "Data.PolyFunction",
          "partialFunction">: meta "Data.PartialFunction",
          "while">: meta "Data.While",
          "do">: meta "Data.Do",
          "for">: meta "Data.For",
          "forYield">: meta "Data.ForYield",
          "new">: meta "Data.New",
          "newAnonymous">: meta "Data.NewAnonymous",
          "placeholder">: meta "Data.Placeholder",
          "eta">: meta "Data.Eta",
          "repeated">: meta "Data.Repeated",
          "param">: meta "Data.Param"],
-- object Data {
--   @branch trait Ref extends Data with scala.meta.Ref
      def "Data.Ref" $
        union [
          "this">: meta "Data.This",
          "super">: meta "Data.Super",
          "name">: meta "Data.Name",
          "anonymous">: meta "Data.Anonymous",
          "select">: meta "Data.Select",
          "applyUnary">: meta "Data.ApplyUnary"],
--   @ast class This(qual: scala.meta.Name) extends Data.Ref
      def "Data.This"
        unit,
--   @ast class Super(thisp: scala.meta.Name, superp: scala.meta.Name) extends Data.Ref
      def "Data.Super" $
        record [
          "thisp">: meta "Name",
          "superp">: meta "Name"],
--   @ast class Name(value: Predef.String @nonEmpty) extends scala.meta.Name with Data.Ref with Pat
      def "Data.Name" $
        record [
          "value">: meta "PredefString"],
--   @ast class Anonymous() extends scala.meta.Name with Data.Ref {
      def "Data.Anonymous"
        unit,
--     def value = ""
--     checkParent(ParentChecks.AnonymousImport)
--   }
--   @ast class Select(qual: Data, name: Data.Name) extends Data.Ref with Pat
      def "Data.Select" $
        record [
          "qual">: meta "Data",
          "name">: meta "Data.Name"],
--   @ast class Interpolate(prefix: Name, parts: List[Lit] @nonEmpty, args: List[Data]) extends Data {
      def "Data.Interpolate" $
        record [
          "prefix">: meta "Data.Name",
          "parts">: list $ meta "Lit",
          "args">: list $ meta "Data"],
--     checkFields(parts.length == args.length + 1)
--   }
--   @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Data]) extends Data {
      def "Data.Xml" $
        record [
          "parts">: list $ meta "Lit",
          "args">: list $ meta "Data"],
--     checkFields(parts.length == args.length + 1)
--   }
--   @ast class Apply(fun: Data, args: List[Data]) extends Data
      def "Data.Apply" $
        record [
          "fun">: meta "Data",
          "args">: list $ meta "Data"],
--   @ast class ApplyUsing(fun: Data, args: List[Data]) extends Data
      def "Data.ApplyUsing" $
        record [
          "fun">: meta "Data",
          "targs">: list $ meta "Data"],
--   @ast class ApplyType(fun: Data, targs: List[Type] @nonEmpty) extends Data
      def "Data.ApplyType" $
        record [
          "lhs">: meta "Data",
          "op">: meta "Data.Name",
          "targs">: list $ meta "Type",
          "args">: list $ meta "Data"],
--   @ast class ApplyInfix(lhs: Data, op: Name, targs: List[Type], args: List[Data]) extends Data
      def "Data.ApplyInfix" $
        record [
          "lhs">: meta "Data",
          "op">: meta "Data.Name",
          "targs">: list $ meta "Type",
          "args">: list $ meta "Data"],
--   @ast class ApplyUnary(op: Name, arg: Data) extends Data.Ref {
      def "Data.ApplyUnary" $
        record [
          "op">: meta "Data.Name",
          "arg">: meta "Data"],
--     checkFields(op.isUnaryOp)
--   }
--   @ast class Assign(lhs: Data, rhs: Data) extends Data {
      def "Data.Assign" $
        record [
          "lhs">: meta "Data",
          "rhs">: meta "Data"],
--     checkFields(lhs.is[Data.Quasi] || lhs.is[Data.Ref] || lhs.is[Data.Apply])
--     checkParent(ParentChecks.DataAssign)
--   }
--   @ast class Return(expr: Data) extends Data
      def "Data.Return" $
        record [
          "expr">: meta "Data"],
--   @ast class Throw(expr: Data) extends Data
      def "Data.Throw" $
        record [
          "expr">: meta "Data"],
--   @ast class Ascribe(expr: Data, tpe: Type) extends Data
      def "Data.Ascribe" $
        record [
          "expr">: meta "Data",
          "tpe">: meta "Type"],
--   @ast class Annotate(expr: Data, annots: List[Mod.Annot] @nonEmpty) extends Data
      def "Data.Annotate" $
        record [
          "expr">: meta "Data",
          "annots">: list $ meta "Mod.Annot"],
--   @ast class Tuple(args: List[Data] @nonEmpty) extends Data {
      def "Data.Tuple" $
        record [
          "args">: list $ meta "Data"],
--     // tuple must have more than one element
--     // however, this element may be Quasi with "hidden" list of elements inside
--     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Data.Quasi]))
--   }
--   @ast class Block(stats: List[Stat]) extends Data {
      def "Data.Block" $
        record [
          "stats">: list $ meta "Stat"],
--     // extension group block can have declarations without body too
--     checkFields(stats.forall(st => st.isBlockStat || st.is[Decl]))
--   }
--   @ast class EndMarker(name: Data.Name) extends Data
      def "Data.EndMarker" $
        record [
          "name">: meta "Data.Name"],
--   @ast class If(cond: Data, thenp: Data, elsep: Data) extends Data {
      def "Data.If" $
        record [
          "cond">: meta "Data",
          "thenp">: meta "Data",
          "elsep">: meta "Data"],
--     @binaryCompatField(since = "4.4.0")
--     private var _mods: List[Mod] = Nil
--   }
--   @ast class QuotedMacroExpr(body: Data) extends Data
      def "Data.QuotedMacroExpr" $
        record [
          "body">: meta "Data"],
--   @ast class QuotedMacroType(tpe: Type) extends Data
      def "Data.QuotedMacroType" $
        record [
          "tpe">: meta "Type"],
--   @ast class SplicedMacroExpr(body: Data) extends Data
      def "Data.SplicedMacroExpr" $
        record [
          "body">: meta "Data"],
--   @ast class Match(expr: Data, cases: List[Case] @nonEmpty) extends Data {
      def "Data.Match" $
        record [
          "expr">: meta "Data",
          "cases">: list $ meta "Case"],
--     @binaryCompatField(since = "4.4.5")
--     private var _mods: List[Mod] = Nil
--   }
--   @ast class Try(expr: Data, catchp: List[Case], finallyp: Option[Data]) extends Data
      def "Data.Try" $
        record [
          "expr">: meta "Data",
          "catchp">: list $ meta "Case",
          "finallyp">: optional $ meta "Data"],
--   @ast class TryWithHandler(expr: Data, catchp: Data, finallyp: Option[Data]) extends Data
      def "Data.TryWithHandler" $
        record [
          "expr">: meta "Data",
          "catchp">: meta "Data",
          "finallyp">: optional $ meta "Data"],
--
--   @branch trait FunctionData extends Data {
      def "Data.FunctionData" $
        union [
          "contextFunction">: meta "Data.ContextFunction",
          "function">: meta "Data.Function"],
--     def params: List[Data.Param]
--     def body: Data
--   }
--   @ast class ContextFunction(params: List[Data.Param], body: Data) extends FunctionData {
      def "Data.ContextFunction" $
        record [
          "params">: list $ meta "Data.Param",
          "body">: meta "Data"],
--     checkFields(
--       params.forall(param =>
--         param.is[Data.Param.Quasi] ||
--           (param.name.is[scala.meta.Name.Anonymous] ==> param.default.isEmpty)
--       )
--     )
--   }
--   @ast class Function(params: List[Data.Param], body: Data) extends FunctionData {
      def "Data.Function" $
        record [
          "params">: list $ meta "Data.Param",
          "body">: meta "Data"],
--     checkFields(
--       params.forall(param =>
--         param.is[Data.Param.Quasi] ||
--           (param.name.is[scala.meta.Name.Anonymous] ==> param.default.isEmpty)
--       )
--     )
--     checkFields(
--       params.exists(_.is[Data.Param.Quasi]) ||
--         params.exists(_.mods.exists(_.is[Mod.Implicit])) ==> (params.length == 1)
--     )
--   }
--   @ast class PolyFunction(tparams: List[Type.Param], body: Data) extends Data
      def "Data.PolyFunction" $
        record [
          "tparams">: list $ meta "Type.Param",
          "body">: meta "Data"],
--   @ast class PartialFunction(cases: List[Case] @nonEmpty) extends Data
      def "Data.PartialFunction" $
        record [
          "cases">: list $ meta "Case"],
--   @ast class While(expr: Data, body: Data) extends Data
      def "Data.While" $
        record [
          "expr">: meta "Data",
          "body">: meta "Data"],
--   @ast class Do(body: Data, expr: Data) extends Data
      def "Data.Do" $
        record [
          "body">: meta "Data",
          "expr">: meta "Data"],
--   @ast class For(enums: List[Enumerator] @nonEmpty, body: Data) extends Data {
      def "Data.For" $
        record [
          "enums">: list $ meta "Enumerator"],
--     checkFields(
--       enums.head.is[Enumerator.Generator] || enums.head.is[Enumerator.CaseGenerator] || enums.head
--         .is[Enumerator.Quasi]
--     )
--   }
--   @ast class ForYield(enums: List[Enumerator] @nonEmpty, body: Data) extends Data
      def "Data.ForYield" $
        record [
          "enums">: list $ meta "Enumerator"],
--   @ast class New(init: Init) extends Data
      def "Data.New" $
        record [
          "init">: meta "Init"],
--   @ast class NewAnonymous(templ: Template) extends Data
      def "Data.NewAnonymous" $
        record [
          "templ">: meta "Template"],
--   @ast class Placeholder() extends Data
      def "Data.Placeholder"
        unit,
--   @ast class Eta(expr: Data) extends Data
      def "Data.Eta" $
        record [
          "expr">: meta "Data"],
--   @ast class Repeated(expr: Data) extends Data {
      def "Data.Repeated" $
        record [
          "expr">: meta "Data"],
--     checkParent(ParentChecks.DataRepeated)
--   }
--   @ast class Param(mods: List[Mod], name: meta.Name, decltpe: Option[Type], default: Option[Data])
--       extends Member
      def "Data.Param" $
        record [
          "mods">: list $ meta "Mod",
          "name">: meta "Name",
          "decltpe">: optional $ meta "Type",
          "default">: optional $ meta "Data"],
--   def fresh(): Data.Name = fresh("fresh")
--   def fresh(prefix: String): Data.Name = Data.Name(prefix + Fresh.nextId())
-- }
--
-- @branch trait Type extends Tree
      def "Type" $
        union [
          "ref">: meta "Type.Ref",
          "anonymousName">: meta "Type.AnonymousName",
          "apply">: meta "Type.Apply",
          "applyInfix">: meta "Type.ApplyInfix",
          "functionType">: meta "Type.FunctionType",
          "polyFunction">: meta "Type.PolyFunction",
          "implicitFunction">: meta "Type.ImplicitFunction",
          "tuple">: meta "Type.Tuple",
          "with">: meta "Type.With",
          "and">: meta "Type.And",
          "or">: meta "Type.Or",
          "refine">: meta "Type.Refine",
          "existential">: meta "Type.Existential",
          "annotate">: meta "Type.Annotate",
          "lambda">: meta "Type.Lambda",
          "macro">: meta "Type.Macro",
          "method">: meta "Type.Method",
          "placeholder">: meta "Type.Placeholder",
          "byName">: meta "Type.ByName",
          "repeated">: meta "Type.Repeated",
          "var">: meta "Type.Var",
          "typedParam">: meta "Type.TypedParam",
          "match">: meta "Type.Match"],
-- object Type {
--   @branch trait Ref extends Type with scala.meta.Ref
      def "Type.Ref" $
        union [
          "name">: meta "Type.Name",
          "select">: meta "Type.Select",
          "project">: meta "Type.Project",
          "singleton">: meta "Type.Singleton"],
--   @ast class Name(value: String @nonEmpty) extends scala.meta.Name with Type.Ref
      def "Type.Name" $
        record [
          "value">: string],
--   @ast class AnonymousName() extends Type
      def "Type.AnonymousName"
        unit,
--   @ast class Select(qual: Data.Ref, name: Type.Name) extends Type.Ref {
      def "Type.Select" $
        record [
          "qual">: meta "Data.Ref",
          "name">: meta "Type.Name"],
--     checkFields(qual.isPath || qual.is[Data.Super] || qual.is[Data.Ref.Quasi])
--   }
--   @ast class Project(qual: Type, name: Type.Name) extends Type.Ref
      def "Type.Project" $
        record [
          "qual">: meta "Type",
          "name">: meta "Type.Name"],
--   @ast class Singleton(ref: Data.Ref) extends Type.Ref {
      def "Type.Singleton" $
        record [
          "ref">: meta "Data.Ref"],
--     checkFields(ref.isPath || ref.is[Data.Super])
--   }
--   @ast class Apply(tpe: Type, args: List[Type] @nonEmpty) extends Type
      def "Type.Apply" $
        record [
          "tpe">: meta "Type",
          "args">: list $ meta "Type"],
--   @ast class ApplyInfix(lhs: Type, op: Name, rhs: Type) extends Type
      def "Type.ApplyInfix" $
        record [
          "lhs">: meta "Type",
          "op">: meta "Type.Name",
          "rhs">: meta "Type"],
--   @branch trait FunctionType extends Type {
      def "Type.FunctionType" $
        union [
          "function">: meta "Type.Function",
          "contextFunction">: meta "Type.ContextFunction"],
--     def params: List[Type]
--     def res: Type
--   }
--   @ast class Function(params: List[Type], res: Type) extends FunctionType
      def "Type.Function" $
        record [
          "params">: list $ meta "Type",
          "res">: meta "Type"],
--   @ast class PolyFunction(tparams: List[Type.Param], tpe: Type) extends Type
      def "Type.PolyFunction" $
        record [
          "tparams">: list $ meta "Type.Param",
          "tpe">: meta "Type"],
--   @ast class ContextFunction(params: List[Type], res: Type) extends FunctionType
      def "Type.ContextFunction" $
        record [
          "params">: list $ meta "Type",
          "res">: meta "Type"],
--   @ast @deprecated("Implicit functions are not supported in any dialect")
--   class ImplicitFunction(
      def "Type.ImplicitFunction" $
        record [
--       params: List[Type],
          "params">: list $ meta "Type",
--       res: Type
          "res">: meta "Type"],
--   ) extends Type
--   @ast class Tuple(args: List[Type] @nonEmpty) extends Type {
      def "Type.Tuple" $
        record [
          "args">: list $ meta "Type"],
--     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Type.Quasi]))
--   }
--   @ast class With(lhs: Type, rhs: Type) extends Type
      def "Type.With" $
        record [
          "lhs">: meta "Type",
          "rhs">: meta "Type"],
--   @ast class And(lhs: Type, rhs: Type) extends Type
      def "Type.And" $
        record [
          "lhs">: meta "Type",
          "rhs">: meta "Type"],
--   @ast class Or(lhs: Type, rhs: Type) extends Type
      def "Type.Or" $
        record [
          "lhs">: meta "Type",
          "rhs">: meta "Type"],
--   @ast class Refine(tpe: Option[Type], stats: List[Stat]) extends Type {
      def "Type.Refine" $
        record [
          "tpe">: optional $ meta "Type",
          "stats">: list $ meta "Stat"],
--     checkFields(stats.forall(_.isRefineStat))
--   }
--   @ast class Existential(tpe: Type, stats: List[Stat] @nonEmpty) extends Type {
      def "Type.Existential" $
        record [
          "tpe">: meta "Type",
          "stats">: list $ meta "Stat"],
--     checkFields(stats.forall(_.isExistentialStat))
--   }
--   @ast class Annotate(tpe: Type, annots: List[Mod.Annot] @nonEmpty) extends Type
      def "Type.Annotate" $
        record [
          "tpe">: meta "Type",
          "annots">: list $ meta "Mod.Annot"],
--   @ast class Lambda(tparams: List[Type.Param], tpe: Type) extends Type {
      def "Type.Lambda" $
        record [
          "tparams">: list $ meta "Type.Param",
          "tpe">: meta "Type"],
--     checkParent(ParentChecks.LambdaType)
--   }
--   @ast class Macro(body: Data) extends Type
      def "Type.Macro" $
        record [
          "body">: meta "Data"],
--   @deprecated("Method type syntax is no longer supported in any dialect", "4.4.3")
--   @ast class Method(paramss: List[List[Data.Param]], tpe: Type) extends Type {
      def "Type.Method" $
        record [
          "paramss">: list $ list $ meta "Data.Param",
          "tpe">: meta "Type"],
--     checkParent(ParentChecks.TypeMethod)
--   }
--   @ast class Placeholder(bounds: Bounds) extends Type
      def "Type.Placeholder" $
        record [
          "bounds">: meta "Type.Bounds"],
--   @ast class Bounds(lo: Option[Type], hi: Option[Type]) extends Tree
      def "Type.Bounds" $
        record [
          "lo">: optional $ meta "Type",
          "hi">: optional $ meta "Type"],
--   @ast class ByName(tpe: Type) extends Type {
      def "Type.ByName" $
        record [
          "tpe">: meta "Type"],
--     checkParent(ParentChecks.TypeByName)
--   }
--   @ast class Repeated(tpe: Type) extends Type {
      def "Type.Repeated" $
        record [
          "tpe">: meta "Type"],
--     checkParent(ParentChecks.TypeRepeated)
--   }
--   @ast class Var(name: Name) extends Type with Member.Type {
      def "Type.Var" $
        record [
          "name">: meta "Type.Name"],
--     checkFields(name.value(0).isLower)
--     checkParent(ParentChecks.TypeVar)
--   }
--
--   @ast class TypedParam(name: Name, typ: Type) extends Type with Member.Type
      def "Type.TypedParam" $
        record [
          "name">: meta "Name",
          "typ">: meta "Type"],
--   @ast class Param(
      def "Type.Param" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: meta.Name,
          "name">: meta "Name",
--       tparams: List[Type.Param],
          "tparams">: list $ meta "Type.Param",
--       tbounds: Type.Bounds,
          "tbounds">: list $ meta "Type.Bounds",
--       vbounds: List[Type],
          "vbounds">: list $ meta "Type",
--       cbounds: List[Type]
          "cbounds">: list $ meta "Type"],
--   ) extends Member
--
--   @ast class Match(tpe: Type, cases: List[TypeCase] @nonEmpty) extends Type
      def "Type.Match" $
        record [
          "tpe">: meta "Type",
          "cases">: list $ meta "TypeCase"],
--   def fresh(): Type.Name = fresh("fresh")
--   def fresh(prefix: String): Type.Name = Type.Name(prefix + Fresh.nextId())
-- }
--
-- @branch trait Pat extends Tree
      def "Pat" $
        union [
          "var">: meta "Pat.Var",
          "wildcard">: unit,
          "seqWildcard">: unit,
          "bind">: meta "Pat.Bind",
          "alternative">: meta "Pat.Alternative",
          "tuple">: meta "Pat.Tuple",
          "repeated">: meta "Pat.Repeated",
          "extract">: meta "Pat.Extract",
          "extractInfix">: meta "Pat.ExtractInfix",
          "interpolate">: meta "Pat.Interpolate",
          "xml">: meta "Pat.Xml",
          "typed">: meta "Pat.Typed",
          "macro">: meta "Pat.Macro",
          "given">: meta "Pat.Given"],
-- object Pat {
--   @ast class Var(name: scala.meta.Data.Name) extends Pat with Member.Data { @
      def "Pat.Var" $
        record [
          "name">: meta "Data.Name"],
--     // NOTE: can't do this check here because of things like `val X = 2`
--     // checkFields(name.value(0).isLower)
--     checkParent(ParentChecks.PatVar)
--   }
--   @ast class Wildcard() extends Pat
--   @ast class SeqWildcard() extends Pat {
--     checkParent(ParentChecks.PatSeqWildcard)
--   }
--   @ast class Bind(lhs: Pat, rhs: Pat) extends Pat {
      def "Pat.Bind" $
        record [
          "lhs">: meta "Pat",
          "rhs">: meta "Pat"],
--     checkFields(lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
--   }
--   @ast class Alternative(lhs: Pat, rhs: Pat) extends Pat
      def "Pat.Alternative" $
        record [
          "lhs">: meta "Pat",
          "rhs">: meta "Pat"],
--   @ast class Tuple(args: List[Pat] @nonEmpty) extends Pat {
      def "Pat.Tuple" $
        record [
          "args">: list $ meta "Pat"],
--     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Pat.Quasi]))
--   }
--   @ast class Repeated(name: scala.meta.Data.Name) extends Pat
      def "Pat.Repeated" $
        record [
          "name">: meta "Data.Name"],
--   @ast class Extract(fun: Data, args: List[Pat]) extends Pat {
      def "Pat.Extract" $
        record [
          "fun">: meta "Data",
          "args">: list $ meta "Pat"],
--     checkFields(fun.isExtractor)
--   }
--   @ast class ExtractInfix(lhs: Pat, op: Data.Name, rhs: List[Pat]) extends Pat
      def "Pat.ExtractInfix" $
        record [
          "lhs">: meta "Pat",
          "op">: meta "Data.Name",
          "rhs">: list $ meta "Pat"],
--   @ast class Interpolate(prefix: Data.Name, parts: List[Lit] @nonEmpty, args: List[Pat])
      def "Pat.Interpolate" $
        record [
          "prefix">: meta "Data.Name",
          "parts">: list $ meta "Lit"],
--       extends Pat {
--     checkFields(parts.length == args.length + 1)
--   }
--   @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
      def "Pat.Xml" $
        record [
          "parts">: list $ meta "Lit",
          "args">: list $ meta "Pat"],
--     checkFields(parts.length == args.length + 1)
--   }
--   @ast class Typed(lhs: Pat, rhs: Type) extends Pat {
      def "Pat.Typed" $
        record [
          "lhs">: meta "Pat",
          "rhs">: meta "Type"],
--     checkFields(!rhs.is[Type.Var] && !rhs.is[Type.Placeholder])
--   }
--   @ast class Macro(body: Data) extends Pat {
      def "Pat.Macro" $
        record [
          "body">: meta "Data"],
--     checkFields(body.is[Data.QuotedMacroExpr] || body.is[Data.QuotedMacroType])
--   }
--   @ast class Given(tpe: Type) extends Pat
      def "Pat.Given" $
        record [
          "tpe">: meta "Type"],
--   def fresh(): Pat.Var = Pat.Var(Data.fresh())
--   def fresh(prefix: String): Pat.Var = Pat.Var(Data.fresh(prefix))
-- }
--
-- @branch trait Member extends Tree {
      def "Member" $
        union [
          "term">: meta "Member.Data",
          "type">: meta "Member.Type",
          "termParam">: meta "Data.Param",
          "typeParam">: meta "Type.Param",
          "self">: meta "Self"],
--   def name: Name
-- }
-- object Member {
--   @branch trait Data extends Member {
      def "Member.Data" $
        union [
          "pkg">: meta "Pkg",
          "object">: meta "Pkg.Object"],
--     def name: scala.meta.Data.Name
--   }
--   @branch trait Type extends Member {
      def "Member.Type" $
        record [
--     def name: scala.meta.Type.Name
          "name">: meta "Type.Name"],
--   }
-- }
--
-- @branch trait Decl extends Stat
      def "Decl" $
        union [
          "val">: meta "Decl.Val",
          "var">: meta "Decl.Var",
          "def">: meta "Decl.Def",
          "type">: meta "Decl.Type",
          "given">: meta "Decl.Given"],
-- object Decl {
--   @ast class Val(mods: List[Mod], pats: List[Pat] @nonEmpty, decltpe: scala.meta.Type) extends Decl
      def "Decl.Val" $
        record [
          "mods">: list $ meta "Mod",
          "pats">: list $ meta "Pat",
          "decltpe">: meta "Type"],
--   @ast class Var(mods: List[Mod], pats: List[Pat] @nonEmpty, decltpe: scala.meta.Type) extends Decl
      def "Decl.Var" $
        record [
          "mods">: list $ meta "Mod",
          "pats">: list $ meta "Pat",
          "decltpe">: meta "Type"],
--   @ast class Def(
      def "Decl.Def" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: Data.Name,
          "name">: meta "Data.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       paramss: List[List[Data.Param]],
          "paramss">: list $ list $ meta "Data.Param",
--       decltpe: scala.meta.Type
          "decltpe">: meta "Type"],
--   ) extends Decl with Member.Data @
      --   @ast class Type(
      def "Decl.Type" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: scala.meta.Type.Name,
          "name">: meta "Type.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       bounds: scala.meta.Type.Bounds
          "bounds">: meta "Type.Bounds"],
--   ) extends Decl with Member.Type
--   @ast class Given(
      def "Decl.Given" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: Data.Name,
          "name">: meta "Data.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       sparams: List[List[Data.Param]],
          "sparams">: list $ list $ meta "Data.Param",
--       decltpe: scala.meta.Type
          "decltpe">: meta "Type"],
--   ) extends Decl with Member.Data @
-- }
--
-- @branch trait Defn extends Stat
      def "Defn" $
        union [
          "val">: meta "Defn.Val",
          "var">: meta "Defn.Var",
          "given">: meta "Defn.Given",
          "enum">: meta "Defn.Enum",
          "enumCase">: meta "Defn.EnumCase",
          "repeatedEnumCase">: meta "Defn.RepeatedEnumCase",
          "givenAlias">: meta "Defn.GivenAlias",
          "extensionGroup">: meta "Defn.ExtensionGroup",
          "def">: meta "Defn.Def",
          "macro">: meta "Defn.Macro",
          "type">: meta "Defn.Type",
          "class">: meta "Defn.Class",
          "trait">: meta "Defn.Trait",
          "object">: meta "Defn.Object"],
-- object Defn {
--   @ast class Val(
      def "Defn.Val" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       pats: List[Pat] @nonEmpty,
          "pats">: list $ meta "Pat",
--       decltpe: Option[scala.meta.Type],
          "decltpe">: optional $ meta "Type",
--       rhs: Data
          "rhs">: meta "Data"],
--   ) extends Defn {
--     checkFields(pats.forall(!_.is[Data.Name]))
--   }
--   @ast class Var(
      def "Defn.Var" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       pats: List[Pat] @nonEmpty,
          "pats">: list $ meta "Pat",
--       decltpe: Option[scala.meta.Type],
          "decltpe">: meta "Type",
--       rhs: Option[Data]
          "rhs">: optional $ meta "Data"],
--   ) extends Defn {
--     checkFields(pats.forall(!_.is[Data.Name]))
--     checkFields(decltpe.nonEmpty || rhs.nonEmpty)
--     checkFields(rhs.isEmpty ==> pats.forall(_.is[Pat.Var]))
--   }
--   @ast class Given(
      def "Defn.Given" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: scala.meta.Name,
          "name">: meta "Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ list $ meta "Type.Param",
--       sparams: List[List[Data.Param]],
          "sparams">: list $ list $ meta "Data.Param",
--       templ: Template
          "templ">: meta "Template"],
--   ) extends Defn
--   @ast class Enum(
      def "Defn.Enum" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: scala.meta.Type.Name,
          "name">: meta "Type.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       ctor: Ctor.Primary,
          "ctor">: meta "Ctor.Primary",
--       templ: Template
          "template">: meta "Template"],
--   ) extends Defn with Member.Type
--   @ast class EnumCase(
      def "Defn.EnumCase" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: Data.Name,
          "name">: meta "Data.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       ctor: Ctor.Primary,
          "ctor">: meta "Ctor.Primary",
--       inits: List[Init]
          "inits">: list $ meta "Init"],
--   ) extends Defn with Member.Data { @
--     checkParent(ParentChecks.EnumCase)
--   }
--   @ast class RepeatedEnumCase(
      def "Defn.RepeatedEnumCase" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       cases: List[Data.Name]
          "cases">: list $ meta "Data.Name"],
--   ) extends Defn {
--     checkParent(ParentChecks.EnumCase)
--   }
--   @ast class GivenAlias(
      def "Defn.GivenAlias" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: scala.meta.Name,
          "name">: meta "Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ list $ meta "Type.Param",
--       sparams: List[List[Data.Param]],
          "sparams">: list $ list $ meta "Data.Param",
--       decltpe: scala.meta.Type,
          "decltpe">: meta "Type",
--       body: Data
          "body">: meta "Data"],
--   ) extends Defn
--   @ast class ExtensionGroup(
      def "Defn.ExtensionGroup" $
        record [
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       paramss: List[List[Data.Param]],
          "parmss">: list $ list $ meta "Data.Param",
--       body: Stat
          "body">: meta "Stat"],
--   ) extends Defn
--   @ast class Def(
      def "Defn.Def" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: Data.Name,
          "name">: meta "Data.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       paramss: List[List[Data.Param]],
          "paramss">: list $ list $ meta "Data.Param",
--       decltpe: Option[scala.meta.Type],
          "decltpe">: optional $ meta "Type",
--       body: Data
          "body">: meta "Data"],
--   ) extends Defn with Member.Data { @
--     checkFields(paramss.forall(onlyLastParamCanBeRepeated))
--   }
--   @ast class Macro(
      def "Defn.Macro" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: Data.Name,
          "name">: meta "Data.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       paramss: List[List[Data.Param]],
          "paramss">: list $ list $ meta "Data.Param",
--       decltpe: Option[scala.meta.Type],
          "decltpe">: optional $ meta "Type",
--       body: Data
          "body">: meta "Data"],
--   ) extends Defn with Member.Data @
--   @ast class Type(
      def "Defn.Type" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: scala.meta.Type.Name,
          "name">: meta "Type.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       body: scala.meta.Type
          "body">: meta "Type"],
--   ) extends Defn with Member.Type {
--     @binaryCompatField("4.4.0")
--     private var _bounds: scala.meta.Type.Bounds = scala.meta.Type.Bounds(None, None)
--   }
--   @ast class Class(
      def "Defn.Class" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: scala.meta.Type.Name,
          "name">: meta "Type.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       ctor: Ctor.Primary,
          "ctor">: meta "Ctor.Primary",
--       templ: Template
          "template">: meta "Template"],
--   ) extends Defn with Member.Type
--   @ast class Trait(
      def "Defn.Trait" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: scala.meta.Type.Name,
          "name">: meta "Type.Name",
--       tparams: List[scala.meta.Type.Param],
          "tparams">: list $ meta "Type.Param",
--       ctor: Ctor.Primary,
          "ctor">: meta "Ctor.Primary",
--       templ: Template
          "template">: meta "Template"],
--   ) extends Defn with Member.Type {
--     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
--   }
--   @ast class Object(mods: List[Mod], name: Data.Name, templ: Template)
      def "Defn.Object" $
        record [
          "name">: meta "Data.Name"], --  from Member.Data
--       extends Defn with Member.Data { @
--     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
--   }
-- }
--
-- @ast class Pkg(ref: Data.Ref, stats: List[Stat]) extends Member.Data with Stat { @
      def "Pkg" $
        record [
          "name">: meta "Data.Name", --  from Member.Data
          "ref">: meta "Data.Ref",
          "stats">: list $ meta "Stat"],
--   checkFields(ref.isQualId)
--   def name: Data.Name = ref match {
--     case name: Data.Name => name
--     case Data.Select(_, name: Data.Name) => name
--   }
-- }
-- object Pkg {
--   @ast class Object(mods: List[Mod], name: Data.Name, templ: Template)
--       extends Member.Data with Stat { @
      def "Pkg.Object" $
        record [
          "mods">: list $ meta "Mod",
          "name">: meta "Data.Name",
          "template">: meta "Template"],
--     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
--   }
-- }
--
-- // NOTE: The names of Ctor.Primary and Ctor.Secondary here is always Name.Anonymous.
-- // While seemingly useless, this name is crucial to one of the key principles behind the semantic API:
-- // "every definition and every reference should carry a name".
-- @branch trait Ctor extends Tree with Member
      def "Ctor" $
        union [
          "primary">: meta "Ctor.Primary",
          "secondary">: meta "Ctor.Secondary"],
-- object Ctor {
--   @ast class Primary(mods: List[Mod], name: Name, paramss: List[List[Data.Param]]) extends Ctor
      def "Ctor.Primary" $
        record [
          "mods">: list $ meta "Mod",
          "name">: meta "Name",
          "paramss">: list $ list $ meta "Data.Param"],
--   @ast class Secondary(
      def "Ctor.Secondary" $
        record [
--       mods: List[Mod],
          "mods">: list $ meta "Mod",
--       name: Name,
          "name">: meta "Name",
--       paramss: List[List[Data.Param]] @nonEmpty,
          "paramss">: list $ list $ meta "Data.Param",
--       init: Init,
          "init">: meta "Init",
--       stats: List[Stat]
          "stats">: list $ meta "Stat"],
--   ) extends Ctor with Stat {
--     checkFields(stats.forall(_.isBlockStat))
--   }
-- }
--
-- // NOTE: The name here is always Name.Anonymous.
-- // See comments to Ctor.Primary and Ctor.Secondary for justification.
-- @ast class Init(tpe: Type, name: Name, argss: List[List[Data]]) extends Ref {
      def "Init" $
        record [
          "tpe">: meta "Type",
          "name">: meta "Name",
          "argss">: list $ list $ meta "Data"],
--   checkFields(tpe.isConstructable)
--   checkParent(ParentChecks.Init)
-- }
--
-- @ast class Self(name: Name, decltpe: Option[Type]) extends Member
      def "Self"
        unit,
--
-- @ast class Template(
      def "Template" $
        record [
--     early: List[Stat],
          "early">: list $ meta "Stat",
--     inits: List[Init],
          "inits">: list $ meta "Init",
--     self: Self,
          "self">: meta "Self",
--     stats: List[Stat]
          "stats">: list $ meta "Stat"],
-- ) extends Tree {
--   @binaryCompatField("4.4.0")
--   private var _derives: List[Type] = Nil
--   checkFields(early.forall(_.isEarlyStat && inits.nonEmpty))
--   checkFields(stats.forall(_.isTemplateStat))
-- }
--
-- @branch trait Mod extends Tree
      def "Mod" $
        union [
          "annot">: meta "Mod.Annot",
          "private">: meta "Mod.Private",
          "protected">: meta "Mod.Protected",
          "implicit">: unit,
          "final">: unit,
          "sealed">: unit,
          "open">: unit,
          "super">: unit,
          "override">: unit,
          "case">: unit,
          "abstract">: unit,
          "covariant">: unit,
          "contravariant">: unit,
          "lazy">: unit,
          "valParam">: unit,
          "varParam">: unit,
          "infix">: unit,
          "inline">: unit,
          "using">: unit,
          "opaque">: unit,
          "transparent">: unit],
-- object Mod {
--   @ast class Annot(init: Init) extends Mod {
      def "Mod.Annot" $
        record [
          "init">: meta "Init"],
--     @deprecated("Use init instead", "1.9.0")
--     def body = init
--   }
--   @ast class Private(within: Ref) extends Mod {
      def "Mod.Private" $
        record [
          "within">: meta "Ref"],
--     checkFields(within.isWithin)
--   }
--   @ast class Protected(within: Ref) extends Mod {
      def "Mod.Protected" $
        record [
          "within">: meta "Ref"],
--     checkFields(within.isWithin)
--   }
--   @ast class Implicit() extends Mod
--   @ast class Final() extends Mod
--   @ast class Sealed() extends Mod
--   @ast class Open() extends Mod
--   @deprecated("Super traits introduced in dotty, but later removed.")
--   @ast class Super() extends Mod
--   @ast class Override() extends Mod
--   @ast class Case() extends Mod
--   @ast class Abstract() extends Mod
--   @ast class Covariant() extends Mod
--   @ast class Contravariant() extends Mod
--   @ast class Lazy() extends Mod
--   @ast class ValParam() extends Mod
--   @ast class VarParam() extends Mod
--   @ast class Infix() extends Mod
--   @ast class Inline() extends Mod
--   @ast class Using() extends Mod
--   @ast class Opaque() extends Mod
--   @ast class Transparent() extends Mod
-- }
--
-- @branch trait Enumerator extends Tree
      def "Enumerator" $
        union [
          "generator">: meta "Enumerator.Generator",
          "caseGenerator">: meta "Enumerator.CaseGenerator",
          "val">: meta "Enumerator.Val",
          "guard">: meta "Enumerator.Guard"],
-- object Enumerator {
--   @ast class Generator(pat: Pat, rhs: Data) extends Enumerator
      def "Enumerator.Generator" $
        record [
          "pat">: meta "Pat",
          "rhs">: meta "Data"],
--   @ast class CaseGenerator(pat: Pat, rhs: Data) extends Enumerator
      def "Enumerator.CaseGenerator" $
        record [
          "pat">: meta "Pat",
          "rhs">: meta "Data"],
--   @ast class Val(pat: Pat, rhs: Data) extends Enumerator
      def "Enumerator.Val" $
        record [
          "pat">: meta "Pat",
          "rhs">: meta "Data"],
--   @ast class Guard(cond: Data) extends Enumerator
      def "Enumerator.Guard" $
        record [
          "cond">: meta "Data"],
-- }
--
-- @branch trait ImportExportStat extends Stat {
      def "ImportExportStat" $
        union [
          "import">: meta "Import",
          "export">: meta "Export"],
--   def importers: List[Importer]
-- }
-- @ast class Import(importers: List[Importer] @nonEmpty) extends ImportExportStat
      def "Import" $
        record [
          "importers">: list $ meta "Importer"],
-- @ast class Export(importers: List[Importer] @nonEmpty) extends ImportExportStat
      def "Export" $
        record [
          "importers">: list $ meta "Importer"],
--
-- @ast class Importer(ref: Data.Ref, importees: List[Importee] @nonEmpty) extends Tree {
      def "Importer" $
        record [
          "ref">: meta "Data.Ref",
          "importees">: list $ meta "Importee"],
--   checkFields(ref.isStableId)
-- }
--
-- @branch trait Importee extends Tree with Ref
      def "Importee" $
        union [
          "wildcard">: unit,
          "given">: meta "Importee.Given",
          "givenAll">: unit,
          "name">: meta "Importee.Name",
          "rename">: meta "Importee.Rename",
          "unimport">: meta "Importee.Unimport"],
-- object Importee {
--   @ast class Wildcard() extends Importee
--   @ast class Given(tpe: Type) extends Importee
      def "Importee.Given" $
        record [
          "tpe">: meta "Type"],
--   @ast class GivenAll() extends Importee
--   @ast class Name(name: scala.meta.Name) extends Importee {
      def "Importee.Name" $
        record [
          "name">: meta "Name"],
--     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
--   }
--   @ast class Rename(name: scala.meta.Name, rename: scala.meta.Name) extends Importee {
      def "Importee.Rename" $
        record [
          "name">: meta "Name",
          "rename">: meta "Name"],
--     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
--     checkFields(rename.is[scala.meta.Name.Quasi] || rename.is[scala.meta.Name.Indeterminate])
--   }
--   @ast class Unimport(name: scala.meta.Name) extends Importee {
      def "Importee.Unimport" $
        record [
          "name">: meta "Name"],
--     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
--   }
-- }
--
-- @branch trait CaseTree extends Tree {
      def "CaseTree" $
        union [
          "case">: meta "Case",
          "typeCase">: meta "TypeCase"],
--   def pat: Tree
--   def body: Tree
-- }
-- @ast class Case(pat: Pat, cond: Option[Data], body: Data) extends CaseTree
      def "Case" $
        record [
          "pat">: meta "Pat",
          "cond">: optional $ meta "Data",
          "body">: meta "Data"],
-- @ast class TypeCase(pat: Type, body: Type) extends CaseTree
      def "TypeCase" $
        record [
          "pat">: meta "Type",
          "body">: meta "Type"],
--
-- @ast class Source(stats: List[Stat]) extends Tree {
      def "Source" $
        record [
          "stats">: list $ meta "Stat"],
--   // NOTE: This validation has been removed to allow dialects with top-level terms.
--   // Ideally, we should push the validation into a dialect-specific prettyprinter when -- 220 is fixed.
--   // checkFields(stats.forall(_.isTopLevelStat))
-- }
--
-- package internal.trees {
--   // NOTE: Quasi is a base trait for a whole bunch of classes.
--   // Every root, branch and ast trait/class among scala.meta trees (except for quasis themselves)
--   // has a corresponding quasi, e.g. Data.Quasi or Type.Quasi.
--   //
--   // Here's how quasis represent unquotes
--   // (XXX below depends on the position where the unquote occurs, e.g. q"$x" will result in Data.Quasi):
--   //   * $x => XXX.Quasi(0, XXX.Name("x"))
--   //   * ..$xs => XXX.Quasi(1, XXX.Quasi(0, XXX.Name("xs"))
--   //   * ...$xss => XXX.Quasi(2, XXX.Quasi(0, XXX.Name("xss"))
--   //   * ..{$fs($args)} => Complex ellipses aren't supported yet
--   @branch trait Quasi extends Tree {
      def "Quasi" --  TODO
        unit]
--     def rank: Int
--     def tree: Tree
--     def pt: Class[_]
--     def become[T <: Quasi: AstInfo]: T
--   }
--
--   @registry object All
-- }
