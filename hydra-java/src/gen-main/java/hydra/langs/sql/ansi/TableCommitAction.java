package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class TableCommitAction implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.TableCommitAction");
  
  private TableCommitAction () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Preserve instance) ;
    
    R visit(Delete instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TableCommitAction instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Preserve instance) {
      return otherwise((instance));
    }
    
    default R visit(Delete instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Preserve extends hydra.langs.sql.ansi.TableCommitAction implements Serializable {
    public Preserve () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Preserve)) {
        return false;
      }
      Preserve o = (Preserve) (other);
      return true;
    }
    
    @Override
    public int hashCode() {
      return 0;
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
  
  public static final class Delete extends hydra.langs.sql.ansi.TableCommitAction implements Serializable {
    public Delete () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Delete)) {
        return false;
      }
      Delete o = (Delete) (other);
      return true;
    }
    
    @Override
    public int hashCode() {
      return 0;
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
}