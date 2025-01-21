# Hydra-Haskell

Hydra is a type-aware data transformation toolkit which aims to be highly flexible and portable.
It has its roots in graph databases and type theory, and provides APIs in Haskell and Java.
See the main Hydra [README](https://github.com/CategoricalData/hydra) for more details.
This Haskell package contains Hydra's Haskell API and Haskell sources specifically.
Releases are available [on Hackage](https://hackage.haskell.org/package/hydra).

## Build

Haskell is the current source-of-truth language for Hydra, which means that most of the Hydra implementation is written either in "raw" Haskell or in a Haskell-based DSL.
You can find the DSL-based sources [here](https://github.com/CategoricalData/hydra/tree/main/hydra-haskell/src/main/haskell/Hydra/Impl/Haskell/Sources);
anything written in the DSL is also mapped into the generated Java and Scala sources.
You can find the generated Haskell sources [here](https://github.com/CategoricalData/hydra/tree/main/hydra-haskell/src/gen-main/haskell).
To build Hydra-Haskell and enter the GHCi REPL, use:

```bash
stack ghci
```

## Test

To run all tests at the command line, use:

```bash
stack test
```

If you are familiar with Hydra-Haskell internals and you want to enter the test environment interactively:

```bash
stack ghci hydra:lib hydra:hydra-test
```

Or just `stack ghci hydra:hydra-test` if you want to treat the library as an external dependency.
Now in the REPL, you can access test resources,

```haskell
:t Hydra.TestUtils.termTestContext
```

or run individual Hspec test cases.

```haskell
hspec Hydra.TermAdaptersSpec.termsAreAdaptedRecursively
```

## Code generation

It is a long-term goal for Hydra to generate its own source code into various languages,
producing nearly-complete Hydra implementations in those languages.
Both Haskell and Java are fully supported as target languages,
which means that all of Hydra's types and programs currently specified in the Haskell DSL are mapped correctly to both Haskell and Java.
Scala support, on the other hand, is partial and experimental at this time.

You can generate Hydra's Haskell sources by first entering the GHCi REPL as above, then:

```haskell
import Hydra.Codegen

writeHaskell "src/gen-main/haskell" mainModules
```

The first argument to `writeHaskell` is the base directory to which the generated files are to be written,
and the second is the list of modules you want to generate (in this case, a special list containing all built-in modules).
For individual modules, use list syntax, e.g.

```haskell
writeHaskell "src/gen-main/haskell" [rdfSyntaxModule, shaclModelModule]
```

To generate test modules, use:

```haskell
writeHaskell "src/gen-test/haskell" testModules
```

Java generation is similar, e.g.

```haskell
writeJava "../hydra-java/src/gen-main/java" mainModules
```

For Java tests, use:

```haskell
writeJava "../hydra-java/src/gen-test/java" testModules
```

Scala generation has known bugs, but you can try it out with:

```haskell
writeScala "../hydra-scala/src/gen-main/scala" kernelModules
```

There is schema-only support for GraphQL:

```haskell
import Hydra.Sources.Langs.Graphql.Syntax
import Hydra.Sources.Langs.Json.Model
writeGraphql "/tmp/graphql" [graphqlSyntaxModule, jsonModelModule]
```

Because GraphQL does not support imports, the GraphQL coder will gather all of the dependencies of a given module together,
and map them to a single `.graphql` file.
Hydra has a similar level of schema-only support for [Protobuf](https://protobuf.dev/):

```haskell
writeProtobuf "/tmp/proto" [jsonModelModule]
```

...and similarly for [PDL](https://linkedin.github.io/rest.li/pdl_schema):

```haskell
writePdl "/tmp/pdl" [jsonModelModule]
```

Note that neither the Protobuf nor PDL coder currently supports polymorphic models.

### JSON and YAML generation

JSON and YAML are slightly different than the languages above, in that they are pure data languages, without accompanying syntax for schemas (types).
Hydra terms can be serialized to either JSON or YAML by first providing a type, then any number of terms corresponding to that type.
For example:

```haskell
:module Hydra.Kernel
import Hydra.Codegen
import Hydra.Langs.Json.Serde
import Hydra.Dsl.Terms as Terms

-- Choose a graph in which to execute flows; we will use the Hydra kernel graph.
g = hydraKernel
flow = fromFlowIo g

-- Choose a type for terms to encode. In this case, we will be encoding numeric precision values.
typ = TypeVariable _Precision

-- Construct an instance of the chosen type. In this case, we construct a precision value, then encode it as a term.
term = Terms.inject _Precision (Field _Precision_bits $ Terms.int32 64)

-- Create the adapting coder
coder <- flow $ jsonStringCoder typ

-- Apply the encoding, which turns the term into a JSON string.
flow (coderEncode coder term) >>= putStrLn
```

For a more sophisticated example involving recursive types, use:

```haskell
typ = TypeVariable _Type
term = Terms.inject _Type (Field _Type_literal $ Terms.inject _LiteralType (Field _LiteralType_boolean $ Terms.record _UnitType []))
```

in place of the `Precision` type and term above.
This defines a type (in this case, the type of all types), and also a term which is an instance of that type (so in this case, an encoded type).

## Haskell API

### Structures

The most important structural types in Hydra are `Type` and `Term` (provided in the generated [Hydra.Core](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/gen-main/haskell/Hydra/Core.hs) module in Haskell),
and `Graph` and `Element` (provided in the generated [Hydra.Mantle](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/gen-main/haskell/Hydra/Mantle.hs) module).
`Type` provides a datatype, and a `Term` is an instance of a known `Type`.
An `Element` is a named term together with its type, and a `Graph` is a collection of elements.
A `Module` is a collection of elements in the same logical namespace, sometimes called a "model" if most of the elements represent type definitions.
The main purpose of Hydra is to define and carry out transformations between graphs,
where those graphs may be almost anything which fits into Hydra's type system -- data, schemas, source code, other transformations, etc.
"Graphs" in the traditional sense are partially supported at this time, including property graphs and RDF graphs.

Types, terms, graphs, elements, and many other entities are parameterized by an annotation type, so you will usually see `Type m`, `Term m`, `Context m`, etc. in the code.
The most common annotation type is called `Meta` (which is just a map of string-valued keys to terms), so you will also encounter `Type Meta`, etc.

### Transformations

Transformations in Hydra take the form of simple functions or, more commonly, expressions involving the `Flow` monad
(a special case of the [State](https://wiki.haskell.org/State_Monad) monad, which has been implemented in many programming languages)
as well as a bidirectional flow called `Coder` and a two-level transformation (types and terms) called `Adapter`.
All of these constructs are provided in the generated [Hydra.Compute](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/gen-main/haskell/Hydra/Compute.hs) module in Haskell,
along with the `Context` type which you will see almost everywhere in Hydra;
a `Context` provides a graph, the schema of that graph (which is itself a graph), a set of primitive functions, an evaluation strategy, and other constructs which are needed for computation.
A context is part of the state which flows through a graph transformation as it is being applied.

In Haskell, you will often see `Flow` and `Context` combined as the `GraphFlow` alias:

```haskell
type GraphFlow m = Flow (Context m)
```

There are two helper types, `FlowState` and `Trace`, which are used together with `Flow`; a `FlowState` is the result of evaluating a `Flow`,
while `Trace` encapsulates a stack trace and error or logger messages.
Since `Flow` is a monad, you can create a `GraphFlow` with `f = pure x`, where `x` is anything you would like to enter into a transformation pipeline.
The transformation is actually applied when you call `unFlow` and pass in a graph context and a trace, i.e.

```haskell
unFlow f cx emptyTrace
```

This gives you a flow state, which you can think of as the exit point of a transformation.
Inside the state object is either a concrete value (if the transformation succeeded) or `Nothing` (if the transformation failed), a stack trace, and a list of messages.
You will always find at least one message if the transformation failed; this is analogous to an exception in mainstream programming languages.

A `Coder`, as mentioned above, is a construct which has a `Flow` in either direction between two types.
As a trivial example, consider this coder which serializes integers to strings using Haskell's built-in `show` function, then reads the strings back to integers using `read`:

```haskell
intStringCoder :: Coder () () Int String
intStringCoder = Coder {
  coderEncode = pure . show,
  coderDecode = pure . read}
```

The `()`'s indicate that this coder is stateless in both directions, which makes the use of `Coder` overkill in this case.
For a more realistic, but still simple example, see the [JSON coder](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Ext/Json/Coder.hs), which makes use of state for error propagation.
For a more sophisticated example, see the [Haskell coder](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Ext/Haskell/Coder.hs)
or the [Java coder](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Ext/Java/Coder.hs);
these make use of all of the facilities of a graph flow, including lexical lookups, type decoding, annotations, etc.

### DSLs

Constructing types and terms directly from the `Type` and `Term` APIs mentioned above is perfectly correct, but not very convenient.
For example, the type of all lists of strings may be expressed as `TypeList $ TypeLiteral LiteralTypeString`,
and a specific instance of that type (a term) may be expressed as `TermList [TermLiteral $ LiteralString "foo", TermLiteral $ LiteralString "bar"]`.

Since all of the work of defining transformations in Hydra consists of specifying types and terms, we make the task (much) easier using domain-specific languages (DSLs).
These DSLs are specific to the host language, so we have Haskell DSLs in hydra-haskell, and (similar, but distinct) Java DSLs in hydra-java.
For example, the type of a list of strings is just `list string` if you include the [Types](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Impl/Haskell/Dsl/Types.hs) DSL,
and the specific list of strings we mentioned is just `list [string "foo", string "bar"]`, or (better yet) `list ["foo", "bar"]` if you include the [Terms](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Impl/Haskell/Dsl/Terms.hs) DSL.
There is additional syntactic sugar in Hydra-Haskell which aims to make defining models and transformations as easy as possible;
see the [Sources](https://github.com/CategoricalData/hydra/tree/main/hydra-haskell/src/main/haskell/Hydra/Impl/Haskell/Sources) directory for many examples.

### Phantom types

A minority of Hydra's primary sources, rather than providing models (type definitions), provide collections of functions.
For example, look at [Basics.hs](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Impl/Haskell/Sources/Basics.hs)
or [Utils.hs](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Impl/Haskell/Sources/Adapters/Utils.hs).
There are not many of these files because the syntax for constructing transformations natively in Hydra DSLs is still in flux,
but you will notice that the type signatures in these modules look very different.
For example, you will see signatures like `Definition (Precision -> String)` which appear to use native Haskell types such as `String`,
or generated types like `Precision`, rather than Hydra's low-level constructs (`Type`, `Term`, etc.).
This is a convenience for the programmer which will will be expanded upon as more of Hydra's kernel (indispensable code which is needed in each host language)
is pulled out of raw Haskell and into the DSLs.
If you are curious how these types work, see the [Phantoms](https://github.com/CategoricalData/hydra/blob/main/hydra-haskell/src/main/haskell/Hydra/Impl/Haskell/Sources/Phantoms.hs) model
and [these slides](https://www.slideshare.net/joshsh/transpilers-gone-wild-introducing-hydra/34).
Phantom types are available both in Haskell and Java.
