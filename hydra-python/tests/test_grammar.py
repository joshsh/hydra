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
    Production,
    Constant,
    Symbol,
    Regex,
)


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
    expression_symbol= Symbol("E")
    expression = PatternNonterminal(expression_symbol)

    term_symbol = Symbol("T")
    term = PatternNonterminal(term_symbol)

    factor_symbol = Symbol("F")
    factor = PatternNonterminal(factor_symbol)

    # Terminal
    plus_symbol = Constant("+")
    plus = PatternConstant(plus_symbol)

    times_symbol = Constant("*")
    times = PatternConstant(times_symbol)

    left_symbol = Constant("(")
    left = PatternConstant(left_symbol)

    right_symbol = Constant(")")
    right = PatternConstant(right_symbol)

    identifier_regex = Regex(r"[a-zA-Z_][a-zA-Z0-9_]*")
    identifier = PatternRegex(identifier_regex)

    # Grammar
    grammar: Grammar = [
        # E -> E + T
        Production(expression_symbol, PatternSequence([expression, plus, term])),
        # E -> T
        Production(expression_symbol, term),
        # T -> T * F
        Production(term_symbol, PatternSequence([term, times, factor])),
        # T -> F
        Production(term_symbol, factor),
        # F -> (E)
        Production(factor_symbol, PatternSequence([left, expression, right])),
        # F -> id
        Production(factor_symbol, identifier),
    ]

    assert grammar
    assert count_nonterminals_in_grammar(grammar) == 3
