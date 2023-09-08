package hydra.langs.shacl.model;

import java.io.Serializable;

/**
 * A number of constraint parameters which are specific to property shapes, and cannot be applied to node shapes
 */
public abstract class PropertyShapeConstraint implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shacl/model.PropertyShapeConstraint");
  
  private PropertyShapeConstraint () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(LessThan instance) ;
    
    R visit(LessThanOrEquals instance) ;
    
    R visit(MaxCount instance) ;
    
    R visit(MinCount instance) ;
    
    R visit(UniqueLang instance) ;
    
    R visit(QualifiedValueShape instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(PropertyShapeConstraint instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(LessThan instance) {
      return otherwise((instance));
    }
    
    default R visit(LessThanOrEquals instance) {
      return otherwise((instance));
    }
    
    default R visit(MaxCount instance) {
      return otherwise((instance));
    }
    
    default R visit(MinCount instance) {
      return otherwise((instance));
    }
    
    default R visit(UniqueLang instance) {
      return otherwise((instance));
    }
    
    default R visit(QualifiedValueShape instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * See https://www.w3.org/TR/shacl/#LessThanConstraintComponent
   */
  public static final class LessThan extends hydra.langs.shacl.model.PropertyShapeConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#LessThanConstraintComponent
     */
    public final java.util.Set<hydra.langs.rdf.syntax.Property> value;
    
    public LessThan (java.util.Set<hydra.langs.rdf.syntax.Property> value) {
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
  
  /**
   * See https://www.w3.org/TR/shacl/#LessThanOrEqualsConstraintComponent
   */
  public static final class LessThanOrEquals extends hydra.langs.shacl.model.PropertyShapeConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#LessThanOrEqualsConstraintComponent
     */
    public final java.util.Set<hydra.langs.rdf.syntax.Property> value;
    
    public LessThanOrEquals (java.util.Set<hydra.langs.rdf.syntax.Property> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof LessThanOrEquals)) {
        return false;
      }
      LessThanOrEquals o = (LessThanOrEquals) (other);
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
  
  /**
   * The maximum cardinality. Node shapes cannot have any value for sh:maxCount. See https://www.w3.org/TR/shacl/#MaxCountConstraintComponent
   */
  public static final class MaxCount extends hydra.langs.shacl.model.PropertyShapeConstraint implements Serializable {
    /**
     * The maximum cardinality. Node shapes cannot have any value for sh:maxCount. See https://www.w3.org/TR/shacl/#MaxCountConstraintComponent
     */
    public final java.math.BigInteger value;
    
    public MaxCount (java.math.BigInteger value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MaxCount)) {
        return false;
      }
      MaxCount o = (MaxCount) (other);
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
  
  /**
   * The minimum cardinality. Node shapes cannot have any value for sh:minCount. See https://www.w3.org/TR/shacl/#MinCountConstraintComponent
   */
  public static final class MinCount extends hydra.langs.shacl.model.PropertyShapeConstraint implements Serializable {
    /**
     * The minimum cardinality. Node shapes cannot have any value for sh:minCount. See https://www.w3.org/TR/shacl/#MinCountConstraintComponent
     */
    public final java.math.BigInteger value;
    
    public MinCount (java.math.BigInteger value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MinCount)) {
        return false;
      }
      MinCount o = (MinCount) (other);
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
  
  /**
   * See https://www.w3.org/TR/shacl/#UniqueLangConstraintComponent
   */
  public static final class UniqueLang extends hydra.langs.shacl.model.PropertyShapeConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#UniqueLangConstraintComponent
     */
    public final Boolean value;
    
    public UniqueLang (Boolean value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof UniqueLang)) {
        return false;
      }
      UniqueLang o = (UniqueLang) (other);
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
  
  /**
   * See https://www.w3.org/TR/shacl/#QualifiedValueShapeConstraintComponent
   */
  public static final class QualifiedValueShape extends hydra.langs.shacl.model.PropertyShapeConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#QualifiedValueShapeConstraintComponent
     */
    public final hydra.langs.shacl.model.QualifiedValueShape value;
    
    public QualifiedValueShape (hydra.langs.shacl.model.QualifiedValueShape value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof QualifiedValueShape)) {
        return false;
      }
      QualifiedValueShape o = (QualifiedValueShape) (other);
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