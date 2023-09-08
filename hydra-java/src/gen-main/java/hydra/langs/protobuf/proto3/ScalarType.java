package hydra.langs.protobuf.proto3;

import java.io.Serializable;

/**
 * One of several Proto3 scalar types
 */
public abstract class ScalarType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.ScalarType");
  
  private ScalarType () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Bool instance) ;
    
    R visit(Bytes instance) ;
    
    R visit(Double_ instance) ;
    
    R visit(Fixed32 instance) ;
    
    R visit(Fixed64 instance) ;
    
    R visit(Float_ instance) ;
    
    R visit(Int32 instance) ;
    
    R visit(Int64 instance) ;
    
    R visit(Sfixed32 instance) ;
    
    R visit(Sfixed64 instance) ;
    
    R visit(Sint32 instance) ;
    
    R visit(Sint64 instance) ;
    
    R visit(String_ instance) ;
    
    R visit(Uint32 instance) ;
    
    R visit(Uint64 instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ScalarType instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Bool instance) {
      return otherwise((instance));
    }
    
    default R visit(Bytes instance) {
      return otherwise((instance));
    }
    
    default R visit(Double_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Fixed32 instance) {
      return otherwise((instance));
    }
    
    default R visit(Fixed64 instance) {
      return otherwise((instance));
    }
    
    default R visit(Float_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Int32 instance) {
      return otherwise((instance));
    }
    
    default R visit(Int64 instance) {
      return otherwise((instance));
    }
    
    default R visit(Sfixed32 instance) {
      return otherwise((instance));
    }
    
    default R visit(Sfixed64 instance) {
      return otherwise((instance));
    }
    
    default R visit(Sint32 instance) {
      return otherwise((instance));
    }
    
    default R visit(Sint64 instance) {
      return otherwise((instance));
    }
    
    default R visit(String_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Uint32 instance) {
      return otherwise((instance));
    }
    
    default R visit(Uint64 instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Bool extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Bool () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Bool)) {
        return false;
      }
      Bool o = (Bool) (other);
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
  
  public static final class Bytes extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Bytes () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Bytes)) {
        return false;
      }
      Bytes o = (Bytes) (other);
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
  
  public static final class Double_ extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Double_ () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Double_)) {
        return false;
      }
      Double_ o = (Double_) (other);
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
  
  public static final class Fixed32 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Fixed32 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Fixed32)) {
        return false;
      }
      Fixed32 o = (Fixed32) (other);
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
  
  public static final class Fixed64 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Fixed64 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Fixed64)) {
        return false;
      }
      Fixed64 o = (Fixed64) (other);
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
  
  public static final class Float_ extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Float_ () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Float_)) {
        return false;
      }
      Float_ o = (Float_) (other);
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
  
  public static final class Int32 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Int32 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Int32)) {
        return false;
      }
      Int32 o = (Int32) (other);
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
  
  public static final class Int64 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Int64 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Int64)) {
        return false;
      }
      Int64 o = (Int64) (other);
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
  
  public static final class Sfixed32 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Sfixed32 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sfixed32)) {
        return false;
      }
      Sfixed32 o = (Sfixed32) (other);
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
  
  public static final class Sfixed64 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Sfixed64 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sfixed64)) {
        return false;
      }
      Sfixed64 o = (Sfixed64) (other);
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
  
  public static final class Sint32 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Sint32 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sint32)) {
        return false;
      }
      Sint32 o = (Sint32) (other);
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
  
  public static final class Sint64 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Sint64 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Sint64)) {
        return false;
      }
      Sint64 o = (Sint64) (other);
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
  
  public static final class String_ extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public String_ () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof String_)) {
        return false;
      }
      String_ o = (String_) (other);
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
  
  public static final class Uint32 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Uint32 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Uint32)) {
        return false;
      }
      Uint32 o = (Uint32) (other);
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
  
  public static final class Uint64 extends hydra.langs.protobuf.proto3.ScalarType implements Serializable {
    public Uint64 () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Uint64)) {
        return false;
      }
      Uint64 o = (Uint64) (other);
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