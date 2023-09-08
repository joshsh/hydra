package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class GlobalOrLocal implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.GlobalOrLocal");
  
  private GlobalOrLocal () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Global instance) ;
    
    R visit(Local instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(GlobalOrLocal instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Global instance) {
      return otherwise((instance));
    }
    
    default R visit(Local instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Global extends hydra.langs.sql.ansi.GlobalOrLocal implements Serializable {
    public Global () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Global)) {
        return false;
      }
      Global o = (Global) (other);
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
  
  public static final class Local extends hydra.langs.sql.ansi.GlobalOrLocal implements Serializable {
    public Local () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Local)) {
        return false;
      }
      Local o = (Local) (other);
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