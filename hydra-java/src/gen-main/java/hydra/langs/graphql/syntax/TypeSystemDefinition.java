package hydra.langs.graphql.syntax;

import java.io.Serializable;

public abstract class TypeSystemDefinition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.TypeSystemDefinition");
  
  private TypeSystemDefinition () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Schema instance) ;
    
    R visit(Type instance) ;
    
    R visit(Directive instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TypeSystemDefinition instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Schema instance) {
      return otherwise((instance));
    }
    
    default R visit(Type instance) {
      return otherwise((instance));
    }
    
    default R visit(Directive instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Schema extends hydra.langs.graphql.syntax.TypeSystemDefinition implements Serializable {
    public final hydra.langs.graphql.syntax.SchemaDefinition value;
    
    public Schema (hydra.langs.graphql.syntax.SchemaDefinition value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Schema)) {
        return false;
      }
      Schema o = (Schema) (other);
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
  
  public static final class Type extends hydra.langs.graphql.syntax.TypeSystemDefinition implements Serializable {
    public final hydra.langs.graphql.syntax.TypeDefinition value;
    
    public Type (hydra.langs.graphql.syntax.TypeDefinition value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Type)) {
        return false;
      }
      Type o = (Type) (other);
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
  
  public static final class Directive extends hydra.langs.graphql.syntax.TypeSystemDefinition implements Serializable {
    public final hydra.langs.graphql.syntax.DirectiveDefinition value;
    
    public Directive (hydra.langs.graphql.syntax.DirectiveDefinition value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Directive)) {
        return false;
      }
      Directive o = (Directive) (other);
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