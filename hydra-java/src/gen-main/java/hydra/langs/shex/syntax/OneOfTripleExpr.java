package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class OneOfTripleExpr implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.OneOfTripleExpr");
  
  private OneOfTripleExpr () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(GroupTripleExpr instance) ;
    
    R visit(MultiElementOneOf instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(OneOfTripleExpr instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(GroupTripleExpr instance) {
      return otherwise((instance));
    }
    
    default R visit(MultiElementOneOf instance) {
      return otherwise((instance));
    }
  }
  
  public static final class GroupTripleExpr extends hydra.langs.shex.syntax.OneOfTripleExpr implements Serializable {
    public final hydra.langs.shex.syntax.GroupTripleExpr value;
    
    public GroupTripleExpr (hydra.langs.shex.syntax.GroupTripleExpr value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof GroupTripleExpr)) {
        return false;
      }
      GroupTripleExpr o = (GroupTripleExpr) (other);
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
  
  public static final class MultiElementOneOf extends hydra.langs.shex.syntax.OneOfTripleExpr implements Serializable {
    public final hydra.langs.shex.syntax.MultiElementOneOf value;
    
    public MultiElementOneOf (hydra.langs.shex.syntax.MultiElementOneOf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MultiElementOneOf)) {
        return false;
      }
      MultiElementOneOf o = (MultiElementOneOf) (other);
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