package hydra.ext.java.syntax;

public abstract class RelationalExpression {
  private RelationalExpression () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Simple instance) ;
    
    R visit(LessThan instance) ;
    
    R visit(GreaterThan instance) ;
    
    R visit(LessThanEqual instance) ;
    
    R visit(GreaterThanEqual instance) ;
    
    R visit(Instanceof instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(RelationalExpression instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Simple instance) {
      return otherwise((instance));
    }
    
    default R visit(LessThan instance) {
      return otherwise((instance));
    }
    
    default R visit(GreaterThan instance) {
      return otherwise((instance));
    }
    
    default R visit(LessThanEqual instance) {
      return otherwise((instance));
    }
    
    default R visit(GreaterThanEqual instance) {
      return otherwise((instance));
    }
    
    default R visit(Instanceof instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Simple extends RelationalExpression {
    public final ShiftExpression value;
    
    public Simple (ShiftExpression value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Simple)) {
        return false;
      }
      Simple o = (Simple) (other);
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
  
  public static final class LessThan extends RelationalExpression {
    public final RelationalExpression_LessThan value;
    
    public LessThan (RelationalExpression_LessThan value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof LessThan)) {
        return false;
      }
      LessThan o = (LessThan) (other);
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
  
  public static final class GreaterThan extends RelationalExpression {
    public final RelationalExpression_GreaterThan value;
    
    public GreaterThan (RelationalExpression_GreaterThan value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof GreaterThan)) {
        return false;
      }
      GreaterThan o = (GreaterThan) (other);
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
  
  public static final class LessThanEqual extends RelationalExpression {
    public final RelationalExpression_LessThanEqual value;
    
    public LessThanEqual (RelationalExpression_LessThanEqual value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof LessThanEqual)) {
        return false;
      }
      LessThanEqual o = (LessThanEqual) (other);
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
  
  public static final class GreaterThanEqual extends RelationalExpression {
    public final RelationalExpression_GreaterThanEqual value;
    
    public GreaterThanEqual (RelationalExpression_GreaterThanEqual value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof GreaterThanEqual)) {
        return false;
      }
      GreaterThanEqual o = (GreaterThanEqual) (other);
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
  
  public static final class Instanceof extends RelationalExpression {
    public final RelationalExpression_InstanceOf value;
    
    public Instanceof (RelationalExpression_InstanceOf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Instanceof)) {
        return false;
      }
      Instanceof o = (Instanceof) (other);
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