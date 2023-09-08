package hydra.langs.shacl.model;

import java.io.Serializable;

/**
 * Any of a number of constraint parameters which can be applied either to node or property shapes
 */
public abstract class CommonConstraint implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shacl/model.CommonConstraint");
  
  private CommonConstraint () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(And instance) ;
    
    R visit(Closed instance) ;
    
    R visit(Class_ instance) ;
    
    R visit(Datatype instance) ;
    
    R visit(Disjoint instance) ;
    
    R visit(Equals instance) ;
    
    R visit(HasValue instance) ;
    
    R visit(In instance) ;
    
    R visit(LanguageIn instance) ;
    
    R visit(NodeKind instance) ;
    
    R visit(Node instance) ;
    
    R visit(Not instance) ;
    
    R visit(MaxExclusive instance) ;
    
    R visit(MaxInclusive instance) ;
    
    R visit(MaxLength instance) ;
    
    R visit(MinExclusive instance) ;
    
    R visit(MinInclusive instance) ;
    
    R visit(MinLength instance) ;
    
    R visit(Pattern instance) ;
    
    R visit(Property instance) ;
    
    R visit(Or instance) ;
    
    R visit(Xone instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(CommonConstraint instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(And instance) {
      return otherwise((instance));
    }
    
    default R visit(Closed instance) {
      return otherwise((instance));
    }
    
    default R visit(Class_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Datatype instance) {
      return otherwise((instance));
    }
    
    default R visit(Disjoint instance) {
      return otherwise((instance));
    }
    
    default R visit(Equals instance) {
      return otherwise((instance));
    }
    
    default R visit(HasValue instance) {
      return otherwise((instance));
    }
    
    default R visit(In instance) {
      return otherwise((instance));
    }
    
    default R visit(LanguageIn instance) {
      return otherwise((instance));
    }
    
    default R visit(NodeKind instance) {
      return otherwise((instance));
    }
    
    default R visit(Node instance) {
      return otherwise((instance));
    }
    
    default R visit(Not instance) {
      return otherwise((instance));
    }
    
    default R visit(MaxExclusive instance) {
      return otherwise((instance));
    }
    
    default R visit(MaxInclusive instance) {
      return otherwise((instance));
    }
    
    default R visit(MaxLength instance) {
      return otherwise((instance));
    }
    
    default R visit(MinExclusive instance) {
      return otherwise((instance));
    }
    
    default R visit(MinInclusive instance) {
      return otherwise((instance));
    }
    
    default R visit(MinLength instance) {
      return otherwise((instance));
    }
    
    default R visit(Pattern instance) {
      return otherwise((instance));
    }
    
    default R visit(Property instance) {
      return otherwise((instance));
    }
    
    default R visit(Or instance) {
      return otherwise((instance));
    }
    
    default R visit(Xone instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * See https://www.w3.org/TR/shacl/#AndConstraintComponent
   */
  public static final class And extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#AndConstraintComponent
     */
    public final java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value;
    
    public And (java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof And)) {
        return false;
      }
      And o = (And) (other);
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
   * See https://www.w3.org/TR/shacl/#ClosedConstraintComponent
   */
  public static final class Closed extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#ClosedConstraintComponent
     */
    public final hydra.langs.shacl.model.Closed value;
    
    public Closed (hydra.langs.shacl.model.Closed value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Closed)) {
        return false;
      }
      Closed o = (Closed) (other);
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
   * See https://www.w3.org/TR/shacl/#ClassConstraintComponent
   */
  public static final class Class_ extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#ClassConstraintComponent
     */
    public final java.util.Set<hydra.langs.rdf.syntax.RdfsClass> value;
    
    public Class_ (java.util.Set<hydra.langs.rdf.syntax.RdfsClass> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Class_)) {
        return false;
      }
      Class_ o = (Class_) (other);
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
   * See https://www.w3.org/TR/shacl/#DatatypeConstraintComponent
   */
  public static final class Datatype extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#DatatypeConstraintComponent
     */
    public final hydra.langs.rdf.syntax.Iri value;
    
    public Datatype (hydra.langs.rdf.syntax.Iri value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Datatype)) {
        return false;
      }
      Datatype o = (Datatype) (other);
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
   * See https://www.w3.org/TR/shacl/#DisjointConstraintComponent
   */
  public static final class Disjoint extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#DisjointConstraintComponent
     */
    public final java.util.Set<hydra.langs.rdf.syntax.Property> value;
    
    public Disjoint (java.util.Set<hydra.langs.rdf.syntax.Property> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Disjoint)) {
        return false;
      }
      Disjoint o = (Disjoint) (other);
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
   * See https://www.w3.org/TR/shacl/#EqualsConstraintComponent
   */
  public static final class Equals extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#EqualsConstraintComponent
     */
    public final java.util.Set<hydra.langs.rdf.syntax.Property> value;
    
    public Equals (java.util.Set<hydra.langs.rdf.syntax.Property> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Equals)) {
        return false;
      }
      Equals o = (Equals) (other);
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
   * Specifies the condition that at least one value node is equal to the given RDF term. See https://www.w3.org/TR/shacl/#HasValueConstraintComponent
   */
  public static final class HasValue extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * Specifies the condition that at least one value node is equal to the given RDF term. See https://www.w3.org/TR/shacl/#HasValueConstraintComponent
     */
    public final java.util.Set<hydra.langs.rdf.syntax.Node> value;
    
    public HasValue (java.util.Set<hydra.langs.rdf.syntax.Node> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof HasValue)) {
        return false;
      }
      HasValue o = (HasValue) (other);
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
   * Specifies the condition that each value node is a member of a provided SHACL list. See https://www.w3.org/TR/shacl/#InConstraintComponent
   */
  public static final class In extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * Specifies the condition that each value node is a member of a provided SHACL list. See https://www.w3.org/TR/shacl/#InConstraintComponent
     */
    public final java.util.List<hydra.langs.rdf.syntax.Node> value;
    
    public In (java.util.List<hydra.langs.rdf.syntax.Node> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof In)) {
        return false;
      }
      In o = (In) (other);
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
   * See https://www.w3.org/TR/shacl/#LanguageInConstraintComponent
   */
  public static final class LanguageIn extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#LanguageInConstraintComponent
     */
    public final java.util.Set<hydra.langs.rdf.syntax.LanguageTag> value;
    
    public LanguageIn (java.util.Set<hydra.langs.rdf.syntax.LanguageTag> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof LanguageIn)) {
        return false;
      }
      LanguageIn o = (LanguageIn) (other);
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
   * See https://www.w3.org/TR/shacl/#NodeKindConstraintComponent
   */
  public static final class NodeKind extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#NodeKindConstraintComponent
     */
    public final hydra.langs.shacl.model.NodeKind value;
    
    public NodeKind (hydra.langs.shacl.model.NodeKind value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NodeKind)) {
        return false;
      }
      NodeKind o = (NodeKind) (other);
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
   * See https://www.w3.org/TR/shacl/#NodeConstraintComponent
   */
  public static final class Node extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#NodeConstraintComponent
     */
    public final java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.NodeShape>> value;
    
    public Node (java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.NodeShape>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Node)) {
        return false;
      }
      Node o = (Node) (other);
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
   * See https://www.w3.org/TR/shacl/#NotConstraintComponent
   */
  public static final class Not extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#NotConstraintComponent
     */
    public final java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value;
    
    public Not (java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Not)) {
        return false;
      }
      Not o = (Not) (other);
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
   * See https://www.w3.org/TR/shacl/#MaxExclusiveConstraintComponent
   */
  public static final class MaxExclusive extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#MaxExclusiveConstraintComponent
     */
    public final hydra.langs.rdf.syntax.Literal value;
    
    public MaxExclusive (hydra.langs.rdf.syntax.Literal value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MaxExclusive)) {
        return false;
      }
      MaxExclusive o = (MaxExclusive) (other);
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
   * See https://www.w3.org/TR/shacl/#MaxInclusiveConstraintComponent
   */
  public static final class MaxInclusive extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#MaxInclusiveConstraintComponent
     */
    public final hydra.langs.rdf.syntax.Literal value;
    
    public MaxInclusive (hydra.langs.rdf.syntax.Literal value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MaxInclusive)) {
        return false;
      }
      MaxInclusive o = (MaxInclusive) (other);
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
   * See https://www.w3.org/TR/shacl/#MaxLengthConstraintComponent
   */
  public static final class MaxLength extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#MaxLengthConstraintComponent
     */
    public final java.math.BigInteger value;
    
    public MaxLength (java.math.BigInteger value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MaxLength)) {
        return false;
      }
      MaxLength o = (MaxLength) (other);
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
   * See https://www.w3.org/TR/shacl/#MinExclusiveConstraintComponent
   */
  public static final class MinExclusive extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#MinExclusiveConstraintComponent
     */
    public final hydra.langs.rdf.syntax.Literal value;
    
    public MinExclusive (hydra.langs.rdf.syntax.Literal value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MinExclusive)) {
        return false;
      }
      MinExclusive o = (MinExclusive) (other);
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
   * See https://www.w3.org/TR/shacl/#MinInclusiveConstraintComponent
   */
  public static final class MinInclusive extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#MinInclusiveConstraintComponent
     */
    public final hydra.langs.rdf.syntax.Literal value;
    
    public MinInclusive (hydra.langs.rdf.syntax.Literal value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MinInclusive)) {
        return false;
      }
      MinInclusive o = (MinInclusive) (other);
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
   * See https://www.w3.org/TR/shacl/#MinLengthConstraintComponent
   */
  public static final class MinLength extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#MinLengthConstraintComponent
     */
    public final java.math.BigInteger value;
    
    public MinLength (java.math.BigInteger value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof MinLength)) {
        return false;
      }
      MinLength o = (MinLength) (other);
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
   * See https://www.w3.org/TR/shacl/#PatternConstraintComponent
   */
  public static final class Pattern extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#PatternConstraintComponent
     */
    public final hydra.langs.shacl.model.Pattern value;
    
    public Pattern (hydra.langs.shacl.model.Pattern value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Pattern)) {
        return false;
      }
      Pattern o = (Pattern) (other);
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
   * See https://www.w3.org/TR/shacl/#PropertyConstraintComponent
   */
  public static final class Property extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#PropertyConstraintComponent
     */
    public final java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.PropertyShape>> value;
    
    public Property (java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.PropertyShape>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Property)) {
        return false;
      }
      Property o = (Property) (other);
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
   * See https://www.w3.org/TR/shacl/#OrConstraintComponent
   */
  public static final class Or extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#OrConstraintComponent
     */
    public final java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value;
    
    public Or (java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Or)) {
        return false;
      }
      Or o = (Or) (other);
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
   * See https://www.w3.org/TR/shacl/#XoneConstraintComponent
   */
  public static final class Xone extends hydra.langs.shacl.model.CommonConstraint implements Serializable {
    /**
     * See https://www.w3.org/TR/shacl/#XoneConstraintComponent
     */
    public final java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value;
    
    public Xone (java.util.Set<hydra.langs.shacl.model.Reference<hydra.langs.shacl.model.Shape>> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Xone)) {
        return false;
      }
      Xone o = (Xone) (other);
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