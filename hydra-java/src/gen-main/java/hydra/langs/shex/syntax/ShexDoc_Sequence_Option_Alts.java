package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class ShexDoc_Sequence_Option_Alts implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.ShexDoc.Sequence.Option.Alts");
  
  private ShexDoc_Sequence_Option_Alts () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(NotStartAction instance) ;
    
    R visit(StartActions instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ShexDoc_Sequence_Option_Alts instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(NotStartAction instance) {
      return otherwise((instance));
    }
    
    default R visit(StartActions instance) {
      return otherwise((instance));
    }
  }
  
  public static final class NotStartAction extends hydra.langs.shex.syntax.ShexDoc_Sequence_Option_Alts implements Serializable {
    public final hydra.langs.shex.syntax.NotStartAction value;
    
    public NotStartAction (hydra.langs.shex.syntax.NotStartAction value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NotStartAction)) {
        return false;
      }
      NotStartAction o = (NotStartAction) (other);
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
  
  public static final class StartActions extends hydra.langs.shex.syntax.ShexDoc_Sequence_Option_Alts implements Serializable {
    public final hydra.langs.shex.syntax.StartActions value;
    
    public StartActions (hydra.langs.shex.syntax.StartActions value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof StartActions)) {
        return false;
      }
      StartActions o = (StartActions) (other);
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