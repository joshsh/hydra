package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class ColumnDefinition_TypeOrDomain_Option implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.ColumnDefinition.TypeOrDomain.Option");
  
  private ColumnDefinition_TypeOrDomain_Option () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(DataType instance) ;
    
    R visit(DomainName instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ColumnDefinition_TypeOrDomain_Option instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(DataType instance) {
      return otherwise((instance));
    }
    
    default R visit(DomainName instance) {
      return otherwise((instance));
    }
  }
  
  public static final class DataType extends hydra.langs.sql.ansi.ColumnDefinition_TypeOrDomain_Option implements Serializable {
    public final hydra.langs.sql.ansi.DataType value;
    
    public DataType (hydra.langs.sql.ansi.DataType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataType)) {
        return false;
      }
      DataType o = (DataType) (other);
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
  
  public static final class DomainName extends hydra.langs.sql.ansi.ColumnDefinition_TypeOrDomain_Option implements Serializable {
    public final hydra.langs.sql.ansi.DomainName value;
    
    public DomainName (hydra.langs.sql.ansi.DomainName value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DomainName)) {
        return false;
      }
      DomainName o = (DomainName) (other);
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