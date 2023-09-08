package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * The algorithm used in Bloom filter.
 */
public abstract class BloomFilterAlgorithm implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.BloomFilterAlgorithm");
  
  private BloomFilterAlgorithm () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Block instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(BloomFilterAlgorithm instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Block instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * Block-based Bloom filter.
   */
  public static final class Block extends hydra.langs.parquet.format.BloomFilterAlgorithm implements Serializable {
    public Block () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Block)) {
        return false;
      }
      Block o = (Block) (other);
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