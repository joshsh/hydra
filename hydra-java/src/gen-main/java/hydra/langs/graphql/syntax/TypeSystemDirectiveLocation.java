package hydra.langs.graphql.syntax;

import java.io.Serializable;

public abstract class TypeSystemDirectiveLocation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/graphql/syntax.TypeSystemDirectiveLocation");
  
  private TypeSystemDirectiveLocation () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(SCHEMA instance) ;
    
    R visit(SCALAR instance) ;
    
    R visit(OBJECT instance) ;
    
    R visit(FIELDLowbarDEFINITION instance) ;
    
    R visit(ARGUMENTLowbarDEFINITION instance) ;
    
    R visit(INTERFACE instance) ;
    
    R visit(UNION instance) ;
    
    R visit(ENUM instance) ;
    
    R visit(ENUMLowbarVALUE instance) ;
    
    R visit(INPUTLowbarOBJECT instance) ;
    
    R visit(INPUTLowbarFIELDLowbarDEFINITION instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TypeSystemDirectiveLocation instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(SCHEMA instance) {
      return otherwise((instance));
    }
    
    default R visit(SCALAR instance) {
      return otherwise((instance));
    }
    
    default R visit(OBJECT instance) {
      return otherwise((instance));
    }
    
    default R visit(FIELDLowbarDEFINITION instance) {
      return otherwise((instance));
    }
    
    default R visit(ARGUMENTLowbarDEFINITION instance) {
      return otherwise((instance));
    }
    
    default R visit(INTERFACE instance) {
      return otherwise((instance));
    }
    
    default R visit(UNION instance) {
      return otherwise((instance));
    }
    
    default R visit(ENUM instance) {
      return otherwise((instance));
    }
    
    default R visit(ENUMLowbarVALUE instance) {
      return otherwise((instance));
    }
    
    default R visit(INPUTLowbarOBJECT instance) {
      return otherwise((instance));
    }
    
    default R visit(INPUTLowbarFIELDLowbarDEFINITION instance) {
      return otherwise((instance));
    }
  }
  
  public static final class SCHEMA extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public SCHEMA () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SCHEMA)) {
        return false;
      }
      SCHEMA o = (SCHEMA) (other);
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
  
  public static final class SCALAR extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public SCALAR () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof SCALAR)) {
        return false;
      }
      SCALAR o = (SCALAR) (other);
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
  
  public static final class OBJECT extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public OBJECT () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof OBJECT)) {
        return false;
      }
      OBJECT o = (OBJECT) (other);
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
  
  public static final class FIELDLowbarDEFINITION extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public FIELDLowbarDEFINITION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof FIELDLowbarDEFINITION)) {
        return false;
      }
      FIELDLowbarDEFINITION o = (FIELDLowbarDEFINITION) (other);
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
  
  public static final class ARGUMENTLowbarDEFINITION extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public ARGUMENTLowbarDEFINITION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ARGUMENTLowbarDEFINITION)) {
        return false;
      }
      ARGUMENTLowbarDEFINITION o = (ARGUMENTLowbarDEFINITION) (other);
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
  
  public static final class INTERFACE extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public INTERFACE () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof INTERFACE)) {
        return false;
      }
      INTERFACE o = (INTERFACE) (other);
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
  
  public static final class UNION extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public UNION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof UNION)) {
        return false;
      }
      UNION o = (UNION) (other);
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
  
  public static final class ENUM extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public ENUM () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ENUM)) {
        return false;
      }
      ENUM o = (ENUM) (other);
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
  
  public static final class ENUMLowbarVALUE extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public ENUMLowbarVALUE () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof ENUMLowbarVALUE)) {
        return false;
      }
      ENUMLowbarVALUE o = (ENUMLowbarVALUE) (other);
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
  
  public static final class INPUTLowbarOBJECT extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public INPUTLowbarOBJECT () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof INPUTLowbarOBJECT)) {
        return false;
      }
      INPUTLowbarOBJECT o = (INPUTLowbarOBJECT) (other);
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
  
  public static final class INPUTLowbarFIELDLowbarDEFINITION extends hydra.langs.graphql.syntax.TypeSystemDirectiveLocation implements Serializable {
    public INPUTLowbarFIELDLowbarDEFINITION () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof INPUTLowbarFIELDLowbarDEFINITION)) {
        return false;
      }
      INPUTLowbarFIELDLowbarDEFINITION o = (INPUTLowbarFIELDLowbarDEFINITION) (other);
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