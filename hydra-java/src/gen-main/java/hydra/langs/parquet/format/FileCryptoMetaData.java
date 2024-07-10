// Note: this is an automatically generated file. Do not edit.

package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Crypto metadata for files with encrypted footer
 */
public class FileCryptoMetaData implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.FileCryptoMetaData");
  
  /**
   * Encryption algorithm. This field is only used for files with encrypted footer. Files with plaintext footer store algorithm id inside footer (FileMetaData structure).
   */
  public final hydra.langs.parquet.format.EncryptionAlgorithm encryptionAlgorithm;
  
  public final java.util.Optional<String> keyMetadata;
  
  public FileCryptoMetaData (hydra.langs.parquet.format.EncryptionAlgorithm encryptionAlgorithm, java.util.Optional<String> keyMetadata) {
    if (encryptionAlgorithm == null) {
      throw new IllegalArgumentException("null value for 'encryptionAlgorithm' argument");
    }
    if (keyMetadata == null) {
      throw new IllegalArgumentException("null value for 'keyMetadata' argument");
    }
    this.encryptionAlgorithm = encryptionAlgorithm;
    this.keyMetadata = keyMetadata;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FileCryptoMetaData)) {
      return false;
    }
    FileCryptoMetaData o = (FileCryptoMetaData) (other);
    return encryptionAlgorithm.equals(o.encryptionAlgorithm) && keyMetadata.equals(o.keyMetadata);
  }
  
  @Override
  public int hashCode() {
    return 2 * encryptionAlgorithm.hashCode() + 3 * keyMetadata.hashCode();
  }
  
  public FileCryptoMetaData withEncryptionAlgorithm(hydra.langs.parquet.format.EncryptionAlgorithm encryptionAlgorithm) {
    if (encryptionAlgorithm == null) {
      throw new IllegalArgumentException("null value for 'encryptionAlgorithm' argument");
    }
    return new FileCryptoMetaData(encryptionAlgorithm, keyMetadata);
  }
  
  public FileCryptoMetaData withKeyMetadata(java.util.Optional<String> keyMetadata) {
    if (keyMetadata == null) {
      throw new IllegalArgumentException("null value for 'keyMetadata' argument");
    }
    return new FileCryptoMetaData(encryptionAlgorithm, keyMetadata);
  }
}