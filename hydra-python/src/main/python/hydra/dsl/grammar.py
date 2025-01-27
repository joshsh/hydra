"""A DSL for building BNF grammars."""

from hydra.grammar import (
    Symbol,
    Pattern,
    PatternLabeled,
    PatternAlternatives,
    Production,
    PatternIgnored,
    PatternSequence,
    PatternNil,
    PatternOption,
    PatternPlus,
    PatternRegex,
    LabeledPattern,
    Label,
    Regex,
    PatternStar,
    PatternConstant,
    Constant,
    PatternNonterminal,
)


def labeled(label: str, pattern: Pattern) -> Pattern:
    """Construct a labeled pattern."""
    return PatternLabeled(LabeledPattern(Label(label), pattern))


def alts(patterns: list[Pattern]) -> Pattern:
    """Construct an alternatives pattern."""
    return PatternAlternatives(patterns)


def define(s: str, patterns: list[Pattern]) -> Production:
    """Construct a production rule."""
    pat = patterns[0] if len(patterns) == 1 else alts(patterns)
    return Production(Symbol(s), pat)


def ignored(pattern: Pattern) -> Pattern:
    """Construct an ignored pattern."""
    return PatternIgnored(pattern)


def sequence(patterns: list[Pattern]) -> Pattern:
    """Construct a sequence pattern."""
    return PatternSequence(patterns)


def nil() -> Pattern:
    """Construct a nil pattern."""
    return PatternNil(None)


def opt(pattern: Pattern) -> Pattern:
    """Construct an optional pattern."""
    return PatternOption(pattern)


def plus(pattern: Pattern) -> Pattern:
    """Construct a plus pattern."""
    return PatternPlus(pattern)


def regex(s: str) -> Pattern:
    """Construct a regex pattern."""
    return PatternRegex(Regex(s))


def star(pattern: Pattern) -> Pattern:
    """Construct a star pattern."""
    return PatternStar(pattern)


def sep(separator: Pattern, pattern: Pattern) -> Pattern:
    """Match patterns like "foo.bar.quux" or "one; two; three; four."""
    return sequence([pattern, star(sequence([separator, pattern]))])


def sepp(separator: Pattern, pattern: Pattern) -> Pattern:
    """Match patterns like "foo.bar.quux" or "foo.bar.quux." (i.e. trailing separators are allowed)."""
    return sequence([pattern, star(sequence([separator, pattern])), opt(separator)])


def symbol(s: str) -> Pattern:
    """Construct a symbol."""
    return PatternNonterminal(Symbol(s))


def terminal(s: str) -> Pattern:
    """Construct a terminal."""
    return PatternConstant(Constant(s))
