package hydra.langs.graphql.syntax;

import java.io.Serializable;

public abstract class Selection implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.Selection");
  
  private Selection () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Field instance) ;
    
    R visit(FragmentSpread instance) ;
    
    R visit(InlineFragment instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Selection instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Field instance) {
      return otherwise((instance));
    }
    
    default R visit(FragmentSpread instance) {
      return otherwise((instance));
    }
    
    default R visit(InlineFragment instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Field extends hydra.langs.graphql.syntax.Selection implements Serializable {
    public final hydra.langs.graphql.syntax.Field value;
    
    public Field (hydra.langs.graphql.syntax.Field value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Field)) {
        return false;
      }
      Field o = (Field) (other);
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
  
  public static final class FragmentSpread extends hydra.langs.graphql.syntax.Selection implements Serializable {
    public final hydra.langs.graphql.syntax.FragmentSpread value;
    
    public FragmentSpread (hydra.langs.graphql.syntax.FragmentSpread value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof FragmentSpread)) {
        return false;
      }
      FragmentSpread o = (FragmentSpread) (other);
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
  
  public static final class InlineFragment extends hydra.langs.graphql.syntax.Selection implements Serializable {
    public final hydra.langs.graphql.syntax.InlineFragment value;
    
    public InlineFragment (hydra.langs.graphql.syntax.InlineFragment value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof InlineFragment)) {
        return false;
      }
      InlineFragment o = (InlineFragment) (other);
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