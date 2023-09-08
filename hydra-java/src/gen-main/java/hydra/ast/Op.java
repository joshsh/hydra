package hydra.ast;

import java.io.Serializable;

/**
 * An operator symbol
 */
public class Op implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ast.Op");
  
  public final hydra.ast.Symbol symbol;
  
  public final hydra.ast.Padding padding;
  
  public final hydra.ast.Precedence precedence;
  
  public final hydra.ast.Associativity associativity;
  
  public Op (hydra.ast.Symbol symbol, hydra.ast.Padding padding, hydra.ast.Precedence precedence, hydra.ast.Associativity associativity) {
    this.symbol = symbol;
    this.padding = padding;
    this.precedence = precedence;
    this.associativity = associativity;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Op)) {
      return false;
    }
    Op o = (Op) (other);
    return symbol.equals(o.symbol) && padding.equals(o.padding) && precedence.equals(o.precedence) && associativity.equals(o.associativity);
  }
  
  @Override
  public int hashCode() {
    return 2 * symbol.hashCode() + 3 * padding.hashCode() + 5 * precedence.hashCode() + 7 * associativity.hashCode();
  }
  
  public Op withSymbol(hydra.ast.Symbol symbol) {
    return new Op(symbol, padding, precedence, associativity);
  }
  
  public Op withPadding(hydra.ast.Padding padding) {
    return new Op(symbol, padding, precedence, associativity);
  }
  
  public Op withPrecedence(hydra.ast.Precedence precedence) {
    return new Op(symbol, padding, precedence, associativity);
  }
  
  public Op withAssociativity(hydra.ast.Associativity associativity) {
    return new Op(symbol, padding, precedence, associativity);
  }
}