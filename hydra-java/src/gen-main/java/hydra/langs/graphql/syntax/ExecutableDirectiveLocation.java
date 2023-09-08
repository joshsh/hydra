package hydra.langs.graphql.syntax;

import java.io.Serializable;

public abstract class ExecutableDirectiveLocation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.ExecutableDirectiveLocation");
  
  private ExecutableDirectiveLocation () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(QUERY instance) ;
    
    R visit(MUTATION instance) ;
    
    R visit(SUBSCRIPTION instance) ;
    
    R visit(FIELD instance) ;
    
    R visit(FRAGMENTLowbarDEFINITION instance) ;
    
    R visit(FRAGMENTLowbarSPREAD instance) ;
    
    R visit(INLINELowbarFRAGMENT instance) ;
    
    R visit(VARIABLELowbarDEFINITION instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ExecutableDirectiveLocation instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(QUERY instance) {
      return otherwise((instance));
    }
    
    default R visit(MUTATION instance) {
      return otherwise((instance));
    }
    
    default R visit(SUBSCRIPTION instance) {
      return otherwise((instance));
    }
    
    default R visit(FIELD instance) {
      return otherwise((instance));
    }
    
    default R visit(FRAGMENTLowbarDEFINITION instance) {
      return otherwise((instance));
    }
    
    default R visit(FRAGMENTLowbarSPREAD instance) {
      return otherwise((instance));
    }
    
    default R visit(INLINELowbarFRAGMENT instance) {
      return otherwise((instance));
    }
    
    default R visit(VARIABLELowbarDEFINITION instance) {
      return otherwise((instance));
    }
  }
  
  public static final class QUERY extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public QUERY () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof QUERY)) {
        return false;
      }
      QUERY o = (QUERY) (other);
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
  
  public static final class MUTATION extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public MUTATION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MUTATION)) {
        return false;
      }
      MUTATION o = (MUTATION) (other);
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
  
  public static final class SUBSCRIPTION extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public SUBSCRIPTION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SUBSCRIPTION)) {
        return false;
      }
      SUBSCRIPTION o = (SUBSCRIPTION) (other);
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
  
  public static final class FIELD extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public FIELD () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof FIELD)) {
        return false;
      }
      FIELD o = (FIELD) (other);
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
  
  public static final class FRAGMENTLowbarDEFINITION extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public FRAGMENTLowbarDEFINITION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof FRAGMENTLowbarDEFINITION)) {
        return false;
      }
      FRAGMENTLowbarDEFINITION o = (FRAGMENTLowbarDEFINITION) (other);
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
  
  public static final class FRAGMENTLowbarSPREAD extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public FRAGMENTLowbarSPREAD () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof FRAGMENTLowbarSPREAD)) {
        return false;
      }
      FRAGMENTLowbarSPREAD o = (FRAGMENTLowbarSPREAD) (other);
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
  
  public static final class INLINELowbarFRAGMENT extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public INLINELowbarFRAGMENT () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof INLINELowbarFRAGMENT)) {
        return false;
      }
      INLINELowbarFRAGMENT o = (INLINELowbarFRAGMENT) (other);
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
  
  public static final class VARIABLELowbarDEFINITION extends hydra.langs.graphql.syntax.ExecutableDirectiveLocation implements Serializable {
    public VARIABLELowbarDEFINITION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof VARIABLELowbarDEFINITION)) {
        return false;
      }
      VARIABLELowbarDEFINITION o = (VARIABLELowbarDEFINITION) (other);
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