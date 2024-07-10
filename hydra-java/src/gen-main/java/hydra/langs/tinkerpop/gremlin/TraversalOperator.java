// Note: this is an automatically generated file. Do not edit.

package hydra.langs.tinkerpop.gremlin;

import java.io.Serializable;

public abstract class TraversalOperator implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/gremlin.TraversalOperator");
  
  private TraversalOperator () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(AddAll instance) ;
    
    R visit(And instance) ;
    
    R visit(Assign instance) ;
    
    R visit(Div instance) ;
    
    R visit(Max instance) ;
    
    R visit(Min instance) ;
    
    R visit(Minus instance) ;
    
    R visit(Mult instance) ;
    
    R visit(Or instance) ;
    
    R visit(Sum instance) ;
    
    R visit(SumLong instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TraversalOperator instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(AddAll instance) {
      return otherwise((instance));
    }
    
    default R visit(And instance) {
      return otherwise((instance));
    }
    
    default R visit(Assign instance) {
      return otherwise((instance));
    }
    
    default R visit(Div instance) {
      return otherwise((instance));
    }
    
    default R visit(Max instance) {
      return otherwise((instance));
    }
    
    default R visit(Min instance) {
      return otherwise((instance));
    }
    
    default R visit(Minus instance) {
      return otherwise((instance));
    }
    
    default R visit(Mult instance) {
      return otherwise((instance));
    }
    
    default R visit(Or instance) {
      return otherwise((instance));
    }
    
    default R visit(Sum instance) {
      return otherwise((instance));
    }
    
    default R visit(SumLong instance) {
      return otherwise((instance));
    }
  }
  
  public static final class AddAll extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public AddAll () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof AddAll)) {
        return false;
      }
      AddAll o = (AddAll) (other);
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
  
  public static final class And extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public And () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof And)) {
        return false;
      }
      And o = (And) (other);
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
  
  public static final class Assign extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Assign () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Assign)) {
        return false;
      }
      Assign o = (Assign) (other);
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
  
  public static final class Div extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Div () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Div)) {
        return false;
      }
      Div o = (Div) (other);
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
  
  public static final class Max extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Max () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Max)) {
        return false;
      }
      Max o = (Max) (other);
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
  
  public static final class Min extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Min () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Min)) {
        return false;
      }
      Min o = (Min) (other);
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
  
  public static final class Minus extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Minus () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Minus)) {
        return false;
      }
      Minus o = (Minus) (other);
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
  
  public static final class Mult extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Mult () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Mult)) {
        return false;
      }
      Mult o = (Mult) (other);
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
  
  public static final class Or extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Or () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Or)) {
        return false;
      }
      Or o = (Or) (other);
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
  
  public static final class Sum extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public Sum () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sum)) {
        return false;
      }
      Sum o = (Sum) (other);
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
  
  public static final class SumLong extends hydra.langs.tinkerpop.gremlin.TraversalOperator implements Serializable {
    public SumLong () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SumLong)) {
        return false;
      }
      SumLong o = (SumLong) (other);
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