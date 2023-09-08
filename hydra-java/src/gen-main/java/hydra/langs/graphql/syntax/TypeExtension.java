package hydra.langs.graphql.syntax;

import java.io.Serializable;

public abstract class TypeExtension implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.TypeExtension");
  
  private TypeExtension () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Scalar instance) ;
    
    R visit(Object_ instance) ;
    
    R visit(Interface instance) ;
    
    R visit(Union instance) ;
    
    R visit(Enum_ instance) ;
    
    R visit(InputObject instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TypeExtension instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Scalar instance) {
      return otherwise((instance));
    }
    
    default R visit(Object_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Interface instance) {
      return otherwise((instance));
    }
    
    default R visit(Union instance) {
      return otherwise((instance));
    }
    
    default R visit(Enum_ instance) {
      return otherwise((instance));
    }
    
    default R visit(InputObject instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Scalar extends hydra.langs.graphql.syntax.TypeExtension implements Serializable {
    public final hydra.langs.graphql.syntax.ScalarTypeExtension value;
    
    public Scalar (hydra.langs.graphql.syntax.ScalarTypeExtension value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Scalar)) {
        return false;
      }
      Scalar o = (Scalar) (other);
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
  
  public static final class Object_ extends hydra.langs.graphql.syntax.TypeExtension implements Serializable {
    public final hydra.langs.graphql.syntax.ObjectTypeExtension value;
    
    public Object_ (hydra.langs.graphql.syntax.ObjectTypeExtension value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Object_)) {
        return false;
      }
      Object_ o = (Object_) (other);
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
  
  public static final class Interface extends hydra.langs.graphql.syntax.TypeExtension implements Serializable {
    public final hydra.langs.graphql.syntax.InterfaceTypeExtension value;
    
    public Interface (hydra.langs.graphql.syntax.InterfaceTypeExtension value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Interface)) {
        return false;
      }
      Interface o = (Interface) (other);
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
  
  public static final class Union extends hydra.langs.graphql.syntax.TypeExtension implements Serializable {
    public final hydra.langs.graphql.syntax.UnionTypeExtension value;
    
    public Union (hydra.langs.graphql.syntax.UnionTypeExtension value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Union)) {
        return false;
      }
      Union o = (Union) (other);
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
  
  public static final class Enum_ extends hydra.langs.graphql.syntax.TypeExtension implements Serializable {
    public final hydra.langs.graphql.syntax.EnumTypeExtension value;
    
    public Enum_ (hydra.langs.graphql.syntax.EnumTypeExtension value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Enum_)) {
        return false;
      }
      Enum_ o = (Enum_) (other);
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
  
  public static final class InputObject extends hydra.langs.graphql.syntax.TypeExtension implements Serializable {
    public final hydra.langs.graphql.syntax.InputObjectTypeExtension value;
    
    public InputObject (hydra.langs.graphql.syntax.InputObjectTypeExtension value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof InputObject)) {
        return false;
      }
      InputObject o = (InputObject) (other);
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