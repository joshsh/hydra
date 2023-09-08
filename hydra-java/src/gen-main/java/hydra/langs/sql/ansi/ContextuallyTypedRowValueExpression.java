package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class ContextuallyTypedRowValueExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ContextuallyTypedRowValueExpression");
  
  private ContextuallyTypedRowValueExpression () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(SpecialCase instance) ;
    
    R visit(Constructor instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ContextuallyTypedRowValueExpression instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(SpecialCase instance) {
      return otherwise((instance));
    }
    
    default R visit(Constructor instance) {
      return otherwise((instance));
    }
  }
  
  public static final class SpecialCase extends hydra.langs.sql.ansi.ContextuallyTypedRowValueExpression implements Serializable {
    public final hydra.langs.sql.ansi.RowValueSpecialCase value;
    
    public SpecialCase (hydra.langs.sql.ansi.RowValueSpecialCase value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SpecialCase)) {
        return false;
      }
      SpecialCase o = (SpecialCase) (other);
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
  
  public static final class Constructor extends hydra.langs.sql.ansi.ContextuallyTypedRowValueExpression implements Serializable {
    public final hydra.langs.sql.ansi.ContextuallyTypedRowValueConstructor value;
    
    public Constructor (hydra.langs.sql.ansi.ContextuallyTypedRowValueConstructor value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Constructor)) {
        return false;
      }
      Constructor o = (Constructor) (other);
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