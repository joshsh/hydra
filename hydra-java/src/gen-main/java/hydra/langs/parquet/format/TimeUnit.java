package hydra.langs.parquet.format;

import java.io.Serializable;

public abstract class TimeUnit implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.TimeUnit");
  
  private TimeUnit () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Millis instance) ;
    
    R visit(Micros instance) ;
    
    R visit(Nanos instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TimeUnit instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Millis instance) {
      return otherwise((instance));
    }
    
    default R visit(Micros instance) {
      return otherwise((instance));
    }
    
    default R visit(Nanos instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Millis extends hydra.langs.parquet.format.TimeUnit implements Serializable {
    public Millis () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Millis)) {
        return false;
      }
      Millis o = (Millis) (other);
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
  
  public static final class Micros extends hydra.langs.parquet.format.TimeUnit implements Serializable {
    public Micros () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Micros)) {
        return false;
      }
      Micros o = (Micros) (other);
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
  
  public static final class Nanos extends hydra.langs.parquet.format.TimeUnit implements Serializable {
    public Nanos () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Nanos)) {
        return false;
      }
      Nanos o = (Nanos) (other);
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