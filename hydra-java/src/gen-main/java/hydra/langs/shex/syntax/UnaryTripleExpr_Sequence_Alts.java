package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class UnaryTripleExpr_Sequence_Alts implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.UnaryTripleExpr.Sequence.Alts");
  
  private UnaryTripleExpr_Sequence_Alts () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(TripleConstraint instance) ;
    
    R visit(BracketedTripleExpr instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(UnaryTripleExpr_Sequence_Alts instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(TripleConstraint instance) {
      return otherwise((instance));
    }
    
    default R visit(BracketedTripleExpr instance) {
      return otherwise((instance));
    }
  }
  
  public static final class TripleConstraint extends hydra.langs.shex.syntax.UnaryTripleExpr_Sequence_Alts implements Serializable {
    public final hydra.langs.shex.syntax.TripleConstraint value;
    
    public TripleConstraint (hydra.langs.shex.syntax.TripleConstraint value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof TripleConstraint)) {
        return false;
      }
      TripleConstraint o = (TripleConstraint) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
  
  public static final class BracketedTripleExpr extends hydra.langs.shex.syntax.UnaryTripleExpr_Sequence_Alts implements Serializable {
    public final hydra.langs.shex.syntax.BracketedTripleExpr value;
    
    public BracketedTripleExpr (hydra.langs.shex.syntax.BracketedTripleExpr value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof BracketedTripleExpr)) {
        return false;
      }
      BracketedTripleExpr o = (BracketedTripleExpr) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
}