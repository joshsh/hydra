// Note: this is an automatically generated file. Do not edit.

package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class ForStatementNoShortIf implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/java/syntax.ForStatementNoShortIf");
  
  public static final hydra.core.Name FIELD_NAME_BASIC = new hydra.core.Name("basic");
  
  public static final hydra.core.Name FIELD_NAME_ENHANCED = new hydra.core.Name("enhanced");
  
  private ForStatementNoShortIf () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Basic instance) ;
    
    R visit(Enhanced instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ForStatementNoShortIf instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Basic instance) {
      return otherwise((instance));
    }
    
    default R visit(Enhanced instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Basic extends hydra.langs.java.syntax.ForStatementNoShortIf implements Serializable {
    public final hydra.langs.java.syntax.BasicForStatementNoShortIf value;
    
    public Basic (hydra.langs.java.syntax.BasicForStatementNoShortIf value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Basic)) {
        return false;
      }
      Basic o = (Basic) (other);
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
  
  public static final class Enhanced extends hydra.langs.java.syntax.ForStatementNoShortIf implements Serializable {
    public final hydra.langs.java.syntax.EnhancedForStatementNoShortIf value;
    
    public Enhanced (hydra.langs.java.syntax.EnhancedForStatementNoShortIf value) {
      java.util.Objects.requireNonNull((value));
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Enhanced)) {
        return false;
      }
      Enhanced o = (Enhanced) (other);
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