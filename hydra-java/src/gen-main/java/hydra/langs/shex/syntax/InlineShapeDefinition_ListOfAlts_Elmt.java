package hydra.langs.shex.syntax;

import java.io.Serializable;

public abstract class InlineShapeDefinition_ListOfAlts_Elmt implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.InlineShapeDefinition.ListOfAlts.Elmt");
  
  private InlineShapeDefinition_ListOfAlts_Elmt () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(IncludeSet instance) ;
    
    R visit(ExtraPropertySet instance) ;
    
    R visit(CLOSED instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(InlineShapeDefinition_ListOfAlts_Elmt instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(IncludeSet instance) {
      return otherwise((instance));
    }
    
    default R visit(ExtraPropertySet instance) {
      return otherwise((instance));
    }
    
    default R visit(CLOSED instance) {
      return otherwise((instance));
    }
  }
  
  public static final class IncludeSet extends hydra.langs.shex.syntax.InlineShapeDefinition_ListOfAlts_Elmt implements Serializable {
    public final hydra.langs.shex.syntax.IncludeSet value;
    
    public IncludeSet (hydra.langs.shex.syntax.IncludeSet value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof IncludeSet)) {
        return false;
      }
      IncludeSet o = (IncludeSet) (other);
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
  
  public static final class ExtraPropertySet extends hydra.langs.shex.syntax.InlineShapeDefinition_ListOfAlts_Elmt implements Serializable {
    public final hydra.langs.shex.syntax.ExtraPropertySet value;
    
    public ExtraPropertySet (hydra.langs.shex.syntax.ExtraPropertySet value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ExtraPropertySet)) {
        return false;
      }
      ExtraPropertySet o = (ExtraPropertySet) (other);
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
  
  public static final class CLOSED extends hydra.langs.shex.syntax.InlineShapeDefinition_ListOfAlts_Elmt implements Serializable {
    public CLOSED () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof CLOSED)) {
        return false;
      }
      CLOSED o = (CLOSED) (other);
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