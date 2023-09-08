package hydra.langs.parquet.format;

import java.io.Serializable;

public abstract class ColumnCryptoMetaData implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.ColumnCryptoMetaData");
  
  private ColumnCryptoMetaData () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(EncryptionWithFooterKey instance) ;
    
    R visit(EncryptionWithColumnKey instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(ColumnCryptoMetaData instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(EncryptionWithFooterKey instance) {
      return otherwise((instance));
    }
    
    default R visit(EncryptionWithColumnKey instance) {
      return otherwise((instance));
    }
  }
  
  public static final class EncryptionWithFooterKey extends hydra.langs.parquet.format.ColumnCryptoMetaData implements Serializable {
    public final hydra.langs.parquet.format.EncryptionWithFooterKey value;
    
    public EncryptionWithFooterKey (hydra.langs.parquet.format.EncryptionWithFooterKey value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof EncryptionWithFooterKey)) {
        return false;
      }
      EncryptionWithFooterKey o = (EncryptionWithFooterKey) (other);
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
  
  public static final class EncryptionWithColumnKey extends hydra.langs.parquet.format.ColumnCryptoMetaData implements Serializable {
    public final hydra.langs.parquet.format.EncryptionWithColumnKey value;
    
    public EncryptionWithColumnKey (hydra.langs.parquet.format.EncryptionWithColumnKey value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof EncryptionWithColumnKey)) {
        return false;
      }
      EncryptionWithColumnKey o = (EncryptionWithColumnKey) (other);
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