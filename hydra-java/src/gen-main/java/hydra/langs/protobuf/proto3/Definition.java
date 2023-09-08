package hydra.langs.protobuf.proto3;

import java.io.Serializable;

public abstract class Definition implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.Definition");
  
  private Definition () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Enum_ instance) ;
    
    R visit(Message instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(Definition instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Enum_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Message instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Enum_ extends hydra.langs.protobuf.proto3.Definition implements Serializable {
    public final hydra.langs.protobuf.proto3.EnumDefinition value;
    
    public Enum_ (hydra.langs.protobuf.proto3.EnumDefinition value) {
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
  
  public static final class Message extends hydra.langs.protobuf.proto3.Definition implements Serializable {
    public final hydra.langs.protobuf.proto3.MessageDefinition value;
    
    public Message (hydra.langs.protobuf.proto3.MessageDefinition value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Message)) {
        return false;
      }
      Message o = (Message) (other);
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