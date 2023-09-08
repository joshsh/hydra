package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * LogicalType annotations to replace ConvertedType. To maintain compatibility, implementations using LogicalType for a SchemaElement aust also set the corresponding ConvertedType (if any) from the following table.
 */
public abstract class LogicalType implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.LogicalType");
  
  private LogicalType () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(String_ instance) ;
    
    R visit(Map instance) ;
    
    R visit(List instance) ;
    
    R visit(Enum_ instance) ;
    
    R visit(Decimal instance) ;
    
    R visit(Date instance) ;
    
    R visit(Time instance) ;
    
    R visit(Timestamp instance) ;
    
    R visit(Integer_ instance) ;
    
    R visit(Unknown instance) ;
    
    R visit(Json instance) ;
    
    R visit(Bson instance) ;
    
    R visit(Uuid instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(LogicalType instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(String_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Map instance) {
      return otherwise((instance));
    }
    
    default R visit(List instance) {
      return otherwise((instance));
    }
    
    default R visit(Enum_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Decimal instance) {
      return otherwise((instance));
    }
    
    default R visit(Date instance) {
      return otherwise((instance));
    }
    
    default R visit(Time instance) {
      return otherwise((instance));
    }
    
    default R visit(Timestamp instance) {
      return otherwise((instance));
    }
    
    default R visit(Integer_ instance) {
      return otherwise((instance));
    }
    
    default R visit(Unknown instance) {
      return otherwise((instance));
    }
    
    default R visit(Json instance) {
      return otherwise((instance));
    }
    
    default R visit(Bson instance) {
      return otherwise((instance));
    }
    
    default R visit(Uuid instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * use ConvertedType UTF8
   */
  public static final class String_ extends hydra.langs.parquet.format.LogicalType implements Serializable {
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
  
  /**
   * use ConvertedType MAP
   */
  public static final class Map extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public Map () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Map)) {
        return false;
      }
      Map o = (Map) (other);
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
  
  /**
   * use ConvertedType LIST
   */
  public static final class List extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public List () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof List)) {
        return false;
      }
      List o = (List) (other);
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
  
  /**
   * use ConvertedType ENUM
   */
  public static final class Enum_ extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public Enum_ () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Enum_)) {
        return false;
      }
      Enum_ o = (Enum_) (other);
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
  
  /**
   * use ConvertedType DECIMAL + SchemaElement.{scale, precision}
   */
  public static final class Decimal extends hydra.langs.parquet.format.LogicalType implements Serializable {
    /**
     * use ConvertedType DECIMAL + SchemaElement.{scale, precision}
     */
    public final hydra.langs.parquet.format.DecimalType value;
    
    public Decimal (hydra.langs.parquet.format.DecimalType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Decimal)) {
        return false;
      }
      Decimal o = (Decimal) (other);
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
   * use ConvertedType DATE
   */
  public static final class Date extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public Date () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Date)) {
        return false;
      }
      Date o = (Date) (other);
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
  
  /**
   * use ConvertedType TIME_MICROS for TIME(isAdjustedToUTC = *, unit = MICROS). use ConvertedType TIME_MILLIS for TIME(isAdjustedToUTC = *, unit = MILLIS)
   */
  public static final class Time extends hydra.langs.parquet.format.LogicalType implements Serializable {
    /**
     * use ConvertedType TIME_MICROS for TIME(isAdjustedToUTC = *, unit = MICROS). use ConvertedType TIME_MILLIS for TIME(isAdjustedToUTC = *, unit = MILLIS)
     */
    public final hydra.langs.parquet.format.TimeType value;
    
    public Time (hydra.langs.parquet.format.TimeType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Time)) {
        return false;
      }
      Time o = (Time) (other);
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
   * use ConvertedType TIMESTAMP_MICROS for TIMESTAMP(isAdjustedToUTC = *, unit = MICROS). use ConvertedType TIMESTAMP_MILLIS for TIMESTAMP(isAdjustedToUTC = *, unit = MILLIS)
   */
  public static final class Timestamp extends hydra.langs.parquet.format.LogicalType implements Serializable {
    /**
     * use ConvertedType TIMESTAMP_MICROS for TIMESTAMP(isAdjustedToUTC = *, unit = MICROS). use ConvertedType TIMESTAMP_MILLIS for TIMESTAMP(isAdjustedToUTC = *, unit = MILLIS)
     */
    public final hydra.langs.parquet.format.TimestampType value;
    
    public Timestamp (hydra.langs.parquet.format.TimestampType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Timestamp)) {
        return false;
      }
      Timestamp o = (Timestamp) (other);
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
   * use ConvertedType INT_* or UINT_*
   */
  public static final class Integer_ extends hydra.langs.parquet.format.LogicalType implements Serializable {
    /**
     * use ConvertedType INT_* or UINT_*
     */
    public final hydra.langs.parquet.format.IntType value;
    
    public Integer_ (hydra.langs.parquet.format.IntType value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Integer_)) {
        return false;
      }
      Integer_ o = (Integer_) (other);
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
   * no compatible ConvertedType
   */
  public static final class Unknown extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public Unknown () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Unknown)) {
        return false;
      }
      Unknown o = (Unknown) (other);
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
  
  /**
   * use ConvertedType JSON
   */
  public static final class Json extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public Json () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Json)) {
        return false;
      }
      Json o = (Json) (other);
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
  
  /**
   * use ConvertedType BSON
   */
  public static final class Bson extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public Bson () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Bson)) {
        return false;
      }
      Bson o = (Bson) (other);
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
  
  /**
   * no compatible ConvertedType
   */
  public static final class Uuid extends hydra.langs.parquet.format.LogicalType implements Serializable {
    public Uuid () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Uuid)) {
        return false;
      }
      Uuid o = (Uuid) (other);
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