// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class InnerTripleExpr implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/shex/syntax.InnerTripleExpr");
  
  public static final hydra.core.Name FIELD_NAME_MULTI_ELEMENT_GROUP = new hydra.core.Name("multiElementGroup");
  
  public static final hydra.core.Name FIELD_NAME_MULTI_ELEMENT_ONE_OF = new hydra.core.Name("multiElementOneOf");
  
  private InnerTripleExpr () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(MultiElementGroup instance) ;
    
    R visit(MultiElementOneOf instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(InnerTripleExpr instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(MultiElementGroup instance) {
      return otherwise((instance));
    }
    
    default R visit(MultiElementOneOf instance) {
      return otherwise((instance));
    }
  }
  
  public static final class MultiElementGroup extends hydra.langs.shex.syntax.InnerTripleExpr implements Serializable {
    public final hydra.langs.shex.syntax.MultiElementGroup value;
    
    public MultiElementGroup (hydra.langs.shex.syntax.MultiElementGroup value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MultiElementGroup)) {
        return false;
      }
      MultiElementGroup o = (MultiElementGroup) (other);
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
  
  public static final class MultiElementOneOf extends hydra.langs.shex.syntax.InnerTripleExpr implements Serializable {
    public final hydra.langs.shex.syntax.MultiElementOneOf value;
    
    public MultiElementOneOf (hydra.langs.shex.syntax.MultiElementOneOf value) {
      java.util.Objects.requireNonNull((value));
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