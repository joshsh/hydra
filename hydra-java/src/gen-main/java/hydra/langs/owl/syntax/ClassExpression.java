package hydra.langs.owl.syntax;

import java.io.Serializable;

public abstract class ClassExpression implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ClassExpression");
  
  private ClassExpression () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Class_ instance) ;
    
    R visit(DataSomeValuesFrom instance) ;
    
    R visit(DataAllValuesFrom instance) ;
    
    R visit(DataHasValue instance) ;
    
    R visit(DataMinCardinality instance) ;
    
    R visit(DataMaxCardinality instance) ;
    
    R visit(DataExactCardinality instance) ;
    
    R visit(ObjectAllValuesFrom instance) ;
    
    R visit(ObjectExactCardinality instance) ;
    
    R visit(ObjectHasSelf instance) ;
    
    R visit(ObjectHasValue instance) ;
    
    R visit(ObjectIntersectionOf instance) ;
    
    R visit(ObjectMaxCardinality instance) ;
    
    R visit(ObjectMinCardinality instance) ;
    
    R visit(ObjectOneOf instance) ;
    
    R visit(ObjectSomeValuesFrom instance) ;
    
    R visit(ObjectUnionOf instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ClassExpression instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Class_ instance) {
      return otherwise((instance));
    }
    
    default R visit(DataSomeValuesFrom instance) {
      return otherwise((instance));
    }
    
    default R visit(DataAllValuesFrom instance) {
      return otherwise((instance));
    }
    
    default R visit(DataHasValue instance) {
      return otherwise((instance));
    }
    
    default R visit(DataMinCardinality instance) {
      return otherwise((instance));
    }
    
    default R visit(DataMaxCardinality instance) {
      return otherwise((instance));
    }
    
    default R visit(DataExactCardinality instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectAllValuesFrom instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectExactCardinality instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectHasSelf instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectHasValue instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectIntersectionOf instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectMaxCardinality instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectMinCardinality instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectOneOf instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectSomeValuesFrom instance) {
      return otherwise((instance));
    }
    
    default R visit(ObjectUnionOf instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Class_ extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.Class_ value;
    
    public Class_ (hydra.langs.owl.syntax.Class_ value) {
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
  
  public static final class DataSomeValuesFrom extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.DataSomeValuesFrom value;
    
    public DataSomeValuesFrom (hydra.langs.owl.syntax.DataSomeValuesFrom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataSomeValuesFrom)) {
        return false;
      }
      DataSomeValuesFrom o = (DataSomeValuesFrom) (other);
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
  
  public static final class DataAllValuesFrom extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.DataAllValuesFrom value;
    
    public DataAllValuesFrom (hydra.langs.owl.syntax.DataAllValuesFrom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataAllValuesFrom)) {
        return false;
      }
      DataAllValuesFrom o = (DataAllValuesFrom) (other);
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
  
  public static final class DataHasValue extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.DataHasValue value;
    
    public DataHasValue (hydra.langs.owl.syntax.DataHasValue value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataHasValue)) {
        return false;
      }
      DataHasValue o = (DataHasValue) (other);
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
  
  public static final class DataMinCardinality extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.DataMinCardinality value;
    
    public DataMinCardinality (hydra.langs.owl.syntax.DataMinCardinality value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataMinCardinality)) {
        return false;
      }
      DataMinCardinality o = (DataMinCardinality) (other);
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
  
  public static final class DataMaxCardinality extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.DataMaxCardinality value;
    
    public DataMaxCardinality (hydra.langs.owl.syntax.DataMaxCardinality value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataMaxCardinality)) {
        return false;
      }
      DataMaxCardinality o = (DataMaxCardinality) (other);
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
  
  public static final class DataExactCardinality extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.DataExactCardinality value;
    
    public DataExactCardinality (hydra.langs.owl.syntax.DataExactCardinality value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof DataExactCardinality)) {
        return false;
      }
      DataExactCardinality o = (DataExactCardinality) (other);
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
  
  public static final class ObjectAllValuesFrom extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectAllValuesFrom value;
    
    public ObjectAllValuesFrom (hydra.langs.owl.syntax.ObjectAllValuesFrom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectAllValuesFrom)) {
        return false;
      }
      ObjectAllValuesFrom o = (ObjectAllValuesFrom) (other);
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
  
  public static final class ObjectExactCardinality extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectExactCardinality value;
    
    public ObjectExactCardinality (hydra.langs.owl.syntax.ObjectExactCardinality value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectExactCardinality)) {
        return false;
      }
      ObjectExactCardinality o = (ObjectExactCardinality) (other);
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
  
  public static final class ObjectHasSelf extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectHasSelf value;
    
    public ObjectHasSelf (hydra.langs.owl.syntax.ObjectHasSelf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectHasSelf)) {
        return false;
      }
      ObjectHasSelf o = (ObjectHasSelf) (other);
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
  
  public static final class ObjectHasValue extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectHasValue value;
    
    public ObjectHasValue (hydra.langs.owl.syntax.ObjectHasValue value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectHasValue)) {
        return false;
      }
      ObjectHasValue o = (ObjectHasValue) (other);
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
  
  public static final class ObjectIntersectionOf extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectIntersectionOf value;
    
    public ObjectIntersectionOf (hydra.langs.owl.syntax.ObjectIntersectionOf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectIntersectionOf)) {
        return false;
      }
      ObjectIntersectionOf o = (ObjectIntersectionOf) (other);
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
  
  public static final class ObjectMaxCardinality extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectMaxCardinality value;
    
    public ObjectMaxCardinality (hydra.langs.owl.syntax.ObjectMaxCardinality value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectMaxCardinality)) {
        return false;
      }
      ObjectMaxCardinality o = (ObjectMaxCardinality) (other);
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
  
  public static final class ObjectMinCardinality extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectMinCardinality value;
    
    public ObjectMinCardinality (hydra.langs.owl.syntax.ObjectMinCardinality value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectMinCardinality)) {
        return false;
      }
      ObjectMinCardinality o = (ObjectMinCardinality) (other);
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
  
  public static final class ObjectOneOf extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectOneOf value;
    
    public ObjectOneOf (hydra.langs.owl.syntax.ObjectOneOf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectOneOf)) {
        return false;
      }
      ObjectOneOf o = (ObjectOneOf) (other);
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
  
  public static final class ObjectSomeValuesFrom extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectSomeValuesFrom value;
    
    public ObjectSomeValuesFrom (hydra.langs.owl.syntax.ObjectSomeValuesFrom value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectSomeValuesFrom)) {
        return false;
      }
      ObjectSomeValuesFrom o = (ObjectSomeValuesFrom) (other);
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
  
  public static final class ObjectUnionOf extends hydra.langs.owl.syntax.ClassExpression implements Serializable {
    public final hydra.langs.owl.syntax.ObjectUnionOf value;
    
    public ObjectUnionOf (hydra.langs.owl.syntax.ObjectUnionOf value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ObjectUnionOf)) {
        return false;
      }
      ObjectUnionOf o = (ObjectUnionOf) (other);
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