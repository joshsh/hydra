package hydra.langs.graphql.syntax;

import java.io.Serializable;

public abstract class OperationDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.OperationDefinition");
  
  private OperationDefinition () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Sequence instance) ;
    
    R visit(SelectionSet instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(OperationDefinition instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Sequence instance) {
      return otherwise((instance));
    }
    
    default R visit(SelectionSet instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Sequence extends hydra.langs.graphql.syntax.OperationDefinition implements Serializable {
    public final hydra.langs.graphql.syntax.OperationDefinition_Sequence value;
    
    public Sequence (hydra.langs.graphql.syntax.OperationDefinition_Sequence value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sequence)) {
        return false;
      }
      Sequence o = (Sequence) (other);
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
  
  public static final class SelectionSet extends hydra.langs.graphql.syntax.OperationDefinition implements Serializable {
    public final hydra.langs.graphql.syntax.SelectionSet value;
    
    public SelectionSet (hydra.langs.graphql.syntax.SelectionSet value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SelectionSet)) {
        return false;
      }
      SelectionSet o = (SelectionSet) (other);
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