package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class TableContentsSource implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.TableContentsSource");
  
  private TableContentsSource () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(List instance) ;
    
    R visit(Subtable instance) ;
    
    R visit(Subquery instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TableContentsSource instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(List instance) {
      return otherwise((instance));
    }
    
    default R visit(Subtable instance) {
      return otherwise((instance));
    }
    
    default R visit(Subquery instance) {
      return otherwise((instance));
    }
  }
  
  public static final class List extends hydra.langs.sql.ansi.TableContentsSource implements Serializable {
    public final hydra.langs.sql.ansi.TableElementList value;
    
    public List (hydra.langs.sql.ansi.TableElementList value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof List)) {
        return false;
      }
      List o = (List) (other);
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
  
  public static final class Subtable extends hydra.langs.sql.ansi.TableContentsSource implements Serializable {
    public final hydra.langs.sql.ansi.TableContentsSource_Subtable value;
    
    public Subtable (hydra.langs.sql.ansi.TableContentsSource_Subtable value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Subtable)) {
        return false;
      }
      Subtable o = (Subtable) (other);
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
  
  public static final class Subquery extends hydra.langs.sql.ansi.TableContentsSource implements Serializable {
    public final hydra.langs.sql.ansi.AsSubqueryClause value;
    
    public Subquery (hydra.langs.sql.ansi.AsSubqueryClause value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Subquery)) {
        return false;
      }
      Subquery o = (Subquery) (other);
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