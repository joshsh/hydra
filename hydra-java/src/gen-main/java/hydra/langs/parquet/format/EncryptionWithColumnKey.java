package hydra.langs.parquet.format;

import java.io.Serializable;

public class EncryptionWithColumnKey implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.EncryptionWithColumnKey");
  
  /**
   * Column path in schema
   */
  public final java.util.List<String> pathInSchema;
  
  public final java.util.Optional<String> keyMetadata;
  
  public EncryptionWithColumnKey (java.util.List<String> pathInSchema, java.util.Optional<String> keyMetadata) {
    this.pathInSchema = pathInSchema;
    this.keyMetadata = keyMetadata;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof EncryptionWithColumnKey)) {
      return false;
    }
    EncryptionWithColumnKey o = (EncryptionWithColumnKey) (other);
    return pathInSchema.equals(o.pathInSchema) && keyMetadata.equals(o.keyMetadata);
  }
  
  @Override
  public int hashCode() {
    return 2 * pathInSchema.hashCode() + 3 * keyMetadata.hashCode();
  }
  
  public EncryptionWithColumnKey withPathInSchema(java.util.List<String> pathInSchema) {
    return new EncryptionWithColumnKey(pathInSchema, keyMetadata);
  }
  
  public EncryptionWithColumnKey withKeyMetadata(java.util.Optional<String> keyMetadata) {
    return new EncryptionWithColumnKey(pathInSchema, keyMetadata);
  }
}