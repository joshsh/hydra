package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class TableElement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.TableElement");
  
  private TableElement () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Column instance) ;
    
    R visit(TableConstraint instance) ;
    
    R visit(Like instance) ;
    
    R visit(SelfReferencingColumn instance) ;
    
    R visit(ColumOptions instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TableElement instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Column instance) {
      return otherwise((instance));
    }
    
    default R visit(TableConstraint instance) {
      return otherwise((instance));
    }
    
    default R visit(Like instance) {
      return otherwise((instance));
    }
    
    default R visit(SelfReferencingColumn instance) {
      return otherwise((instance));
    }
    
    default R visit(ColumOptions instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Column extends hydra.langs.sql.ansi.TableElement implements Serializable {
    public final hydra.langs.sql.ansi.ColumnDefinition value;
    
    public Column (hydra.langs.sql.ansi.ColumnDefinition value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Column)) {
        return false;
      }
      Column o = (Column) (other);
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
  
  public static final class TableConstraint extends hydra.langs.sql.ansi.TableElement implements Serializable {
    public final hydra.langs.sql.ansi.TableConstraintDefinition value;
    
    public TableConstraint (hydra.langs.sql.ansi.TableConstraintDefinition value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof TableConstraint)) {
        return false;
      }
      TableConstraint o = (TableConstraint) (other);
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
  
  public static final class Like extends hydra.langs.sql.ansi.TableElement implements Serializable {
    public final hydra.langs.sql.ansi.LikeClause value;
    
    public Like (hydra.langs.sql.ansi.LikeClause value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Like)) {
        return false;
      }
      Like o = (Like) (other);
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
  
  public static final class SelfReferencingColumn extends hydra.langs.sql.ansi.TableElement implements Serializable {
    public final hydra.langs.sql.ansi.SelfReferencingColumnSpecification value;
    
    public SelfReferencingColumn (hydra.langs.sql.ansi.SelfReferencingColumnSpecification value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SelfReferencingColumn)) {
        return false;
      }
      SelfReferencingColumn o = (SelfReferencingColumn) (other);
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
  
  public static final class ColumOptions extends hydra.langs.sql.ansi.TableElement implements Serializable {
    public final hydra.langs.sql.ansi.ColumnOptions value;
    
    public ColumOptions (hydra.langs.sql.ansi.ColumnOptions value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ColumOptions)) {
        return false;
      }
      ColumOptions o = (ColumOptions) (other);
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