package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * The hash function used in Bloom filter. This function takes the hash of a column value using plain encoding.
 */
public abstract class BloomFilterHash implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.BloomFilterHash");
  
  private BloomFilterHash () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Xxhash instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(BloomFilterHash instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Xxhash instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * xxHash Strategy.
   */
  public static final class Xxhash extends hydra.langs.parquet.format.BloomFilterHash implements Serializable {
    public Xxhash () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Xxhash)) {
        return false;
      }
      Xxhash o = (Xxhash) (other);
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