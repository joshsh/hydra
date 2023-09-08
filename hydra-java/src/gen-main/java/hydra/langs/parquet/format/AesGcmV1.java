package hydra.langs.parquet.format;

import java.io.Serializable;

public class AesGcmV1 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.AesGcmV1");
  
  public final java.util.Optional<String> aadPrefix;
  
  public final java.util.Optional<String> aadFileUnique;
  
  /**
   * In files encrypted with AAD prefix without storing it, readers must supply the prefix
   */
  public final java.util.Optional<Boolean> supplyAadPrefix;
  
  public AesGcmV1 (java.util.Optional<String> aadPrefix, java.util.Optional<String> aadFileUnique, java.util.Optional<Boolean> supplyAadPrefix) {
    this.aadPrefix = aadPrefix;
    this.aadFileUnique = aadFileUnique;
    this.supplyAadPrefix = supplyAadPrefix;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AesGcmV1)) {
      return false;
    }
    AesGcmV1 o = (AesGcmV1) (other);
    return aadPrefix.equals(o.aadPrefix) && aadFileUnique.equals(o.aadFileUnique) && supplyAadPrefix.equals(o.supplyAadPrefix);
  }
  
  @Override
  public int hashCode() {
    return 2 * aadPrefix.hashCode() + 3 * aadFileUnique.hashCode() + 5 * supplyAadPrefix.hashCode();
  }
  
  public AesGcmV1 withAadPrefix(java.util.Optional<String> aadPrefix) {
    return new AesGcmV1(aadPrefix, aadFileUnique, supplyAadPrefix);
  }
  
  public AesGcmV1 withAadFileUnique(java.util.Optional<String> aadFileUnique) {
    return new AesGcmV1(aadPrefix, aadFileUnique, supplyAadPrefix);
  }
  
  public AesGcmV1 withSupplyAadPrefix(java.util.Optional<Boolean> supplyAadPrefix) {
    return new AesGcmV1(aadPrefix, aadFileUnique, supplyAadPrefix);
  }
}