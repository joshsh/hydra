package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class ImportDeclaration implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.ImportDeclaration");
  
  private ImportDeclaration () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(SingleType instance) ;
    
    R visit(TypeImportOnDemand instance) ;
    
    R visit(SingleStaticImport instance) ;
    
    R visit(StaticImportOnDemand instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ImportDeclaration instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(SingleType instance) {
      return otherwise((instance));
    }
    
    default R visit(TypeImportOnDemand instance) {
      return otherwise((instance));
    }
    
    default R visit(SingleStaticImport instance) {
      return otherwise((instance));
    }
    
    default R visit(StaticImportOnDemand instance) {
      return otherwise((instance));
    }
  }
  
  public static final class SingleType extends hydra.langs.java.syntax.ImportDeclaration implements Serializable {
    public final hydra.langs.java.syntax.SingleTypeImportDeclaration value;
    
    public SingleType (hydra.langs.java.syntax.SingleTypeImportDeclaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SingleType)) {
        return false;
      }
      SingleType o = (SingleType) (other);
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
  
  public static final class TypeImportOnDemand extends hydra.langs.java.syntax.ImportDeclaration implements Serializable {
    public final hydra.langs.java.syntax.TypeImportOnDemandDeclaration value;
    
    public TypeImportOnDemand (hydra.langs.java.syntax.TypeImportOnDemandDeclaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof TypeImportOnDemand)) {
        return false;
      }
      TypeImportOnDemand o = (TypeImportOnDemand) (other);
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
  
  public static final class SingleStaticImport extends hydra.langs.java.syntax.ImportDeclaration implements Serializable {
    public final hydra.langs.java.syntax.SingleStaticImportDeclaration value;
    
    public SingleStaticImport (hydra.langs.java.syntax.SingleStaticImportDeclaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SingleStaticImport)) {
        return false;
      }
      SingleStaticImport o = (SingleStaticImport) (other);
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
  
  public static final class StaticImportOnDemand extends hydra.langs.java.syntax.ImportDeclaration implements Serializable {
    public final hydra.langs.java.syntax.StaticImportOnDemandDeclaration value;
    
    public StaticImportOnDemand (hydra.langs.java.syntax.StaticImportOnDemandDeclaration value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof StaticImportOnDemand)) {
        return false;
      }
      StaticImportOnDemand o = (StaticImportOnDemand) (other);
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