// Note: this is an automatically generated file. Do not edit.

package hydra.langs.haskell.ast;

import java.io.Serializable;

/**
 * An application-style declaration head
 */
public class DeclarationHead_Application implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/haskell/ast.DeclarationHead.Application");
  
  public final hydra.langs.haskell.ast.DeclarationHead function;
  
  public final hydra.langs.haskell.ast.Variable operand;
  
  public DeclarationHead_Application (hydra.langs.haskell.ast.DeclarationHead function, hydra.langs.haskell.ast.Variable operand) {
    if (function == null) {
      throw new IllegalArgumentException("null value for 'function' argument");
    }
    if (operand == null) {
      throw new IllegalArgumentException("null value for 'operand' argument");
    }
    this.function = function;
    this.operand = operand;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof DeclarationHead_Application)) {
      return false;
    }
    DeclarationHead_Application o = (DeclarationHead_Application) (other);
    return function.equals(o.function) && operand.equals(o.operand);
  }
  
  @Override
  public int hashCode() {
    return 2 * function.hashCode() + 3 * operand.hashCode();
  }
  
  public DeclarationHead_Application withFunction(hydra.langs.haskell.ast.DeclarationHead function) {
    if (function == null) {
      throw new IllegalArgumentException("null value for 'function' argument");
    }
    return new DeclarationHead_Application(function, operand);
  }
  
  public DeclarationHead_Application withOperand(hydra.langs.haskell.ast.Variable operand) {
    if (operand == null) {
      throw new IllegalArgumentException("null value for 'operand' argument");
    }
    return new DeclarationHead_Application(function, operand);
  }
}