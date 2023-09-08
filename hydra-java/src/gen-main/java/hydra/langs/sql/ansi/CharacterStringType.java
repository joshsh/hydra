package hydra.langs.sql.ansi;

import java.io.Serializable;

public abstract class CharacterStringType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/sql/ansi.CharacterStringType");
  
  private CharacterStringType () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Character_ instance) ;
    
    R visit(Char instance) ;
    
    R visit(CharacterVarying instance) ;
    
    R visit(CharVarying instance) ;
    
    R visit(Varchar instance) ;
    
    R visit(CharacterLargeObject instance) ;
    
    R visit(CharLargeObject instance) ;
    
    R visit(Clob instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(CharacterStringType instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Character_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Char instance) {
      return otherwise((instance));
    }
    
    default R visit(CharacterVarying instance) {
      return otherwise((instance));
    }
    
    default R visit(CharVarying instance) {
      return otherwise((instance));
    }
    
    default R visit(Varchar instance) {
      return otherwise((instance));
    }
    
    default R visit(CharacterLargeObject instance) {
      return otherwise((instance));
    }
    
    default R visit(CharLargeObject instance) {
      return otherwise((instance));
    }
    
    default R visit(Clob instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Character_ extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.Length> value;
    
    public Character_ (java.util.Optional<hydra.langs.sql.ansi.Length> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Character_)) {
        return false;
      }
      Character_ o = (Character_) (other);
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
  
  public static final class Char extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.Length> value;
    
    public Char (java.util.Optional<hydra.langs.sql.ansi.Length> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Char)) {
        return false;
      }
      Char o = (Char) (other);
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
  
  public static final class CharacterVarying extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final hydra.langs.sql.ansi.Length value;
    
    public CharacterVarying (hydra.langs.sql.ansi.Length value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof CharacterVarying)) {
        return false;
      }
      CharacterVarying o = (CharacterVarying) (other);
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
  
  public static final class CharVarying extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final hydra.langs.sql.ansi.Length value;
    
    public CharVarying (hydra.langs.sql.ansi.Length value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof CharVarying)) {
        return false;
      }
      CharVarying o = (CharVarying) (other);
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
  
  public static final class Varchar extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final hydra.langs.sql.ansi.Length value;
    
    public Varchar (hydra.langs.sql.ansi.Length value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Varchar)) {
        return false;
      }
      Varchar o = (Varchar) (other);
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
  
  public static final class CharacterLargeObject extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value;
    
    public CharacterLargeObject (java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof CharacterLargeObject)) {
        return false;
      }
      CharacterLargeObject o = (CharacterLargeObject) (other);
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
  
  public static final class CharLargeObject extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value;
    
    public CharLargeObject (java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof CharLargeObject)) {
        return false;
      }
      CharLargeObject o = (CharLargeObject) (other);
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
  
  public static final class Clob extends hydra.langs.sql.ansi.CharacterStringType implements Serializable {
    public final java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value;
    
    public Clob (java.util.Optional<hydra.langs.sql.ansi.LargeObjectLength> value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Clob)) {
        return false;
      }
      Clob o = (Clob) (other);
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