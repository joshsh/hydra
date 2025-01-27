from hydra.grammar import (
    Pattern,
    PatternNonterminal,
    PatternSequence,
    PatternAlternatives,
    PatternOption,
    PatternStar,
    PatternPlus,
    PatternLabeled,
    PatternConstant,
    PatternRegex,
    Grammar,
)
import hydra.dsl.grammar as dsl


def gather_nonterminals(pattern: Pattern) -> set[str]:
    """Gather all nonterminals in a pattern."""
    match pattern:
        case PatternNonterminal(value):
            return {value}
        case PatternSequence(value):
            nonterminals: set[str] = set()
            for p in value:
                nonterminals = nonterminals.union(gather_nonterminals(p))
            return nonterminals
        case PatternAlternatives(value):
            nonterminals: set[str] = set()
            for p in value:
                nonterminals = nonterminals.union(gather_nonterminals(p))
            return nonterminals
        case PatternOption(value):
            return gather_nonterminals(value)
        case PatternStar(value):
            return gather_nonterminals(value)
        case PatternPlus(value):
            return gather_nonterminals(value)
        case PatternLabeled(value):
            return gather_nonterminals(value.pattern)
        case PatternConstant(value):
            return set()
        case PatternRegex(value):
            return set()
        case _:
            return set()


def count_nonterminals_in_grammar(grammar: Grammar) -> int:
    """Count the number of nonterminals in a grammar."""
    nonterminals: set[str] = set()
    for production in grammar:
        nonterminals = nonterminals.union(gather_nonterminals(production.pattern))
    return len(nonterminals)


def test_math_grammar():
    # Non-terminal: {E, T, F}
    expression = dsl.symbol("E")
    term = dsl.symbol("T")
    factor = dsl.symbol("F")

    # Terminal
    plus = dsl.terminal("+")
    times = dsl.terminal("*")
    left = dsl.terminal("(")
    right = dsl.terminal(")")
    identifier = dsl.regex(r"[a-zA-Z_][a-zA-Z0-9_]*")

    # Grammar
    grammar: Grammar = [
        # E -> E + T
        dsl.define("E", [expression, plus, term]),
        # E -> T
        dsl.define("E", [term]),
        # T -> T * F
        dsl.define("T", [term, times, factor]),
        # T -> F
        dsl.define("T", [factor]),
        # F -> (E)
        dsl.define("F", [left, expression, right]),
        # F -> id
        dsl.define("F", [identifier]),
    ]

    assert grammar
    assert count_nonterminals_in_grammar(grammar) == 3
