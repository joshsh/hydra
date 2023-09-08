package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * Description for file metadata
 */
public class FileMetaData implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.FileMetaData");
  
  /**
   * Version of this file
   */
  public final Integer version;
  
  /**
   * Parquet schema for this file.  This schema contains metadata for all the columns. The schema is represented as a tree with a single root.  The nodes of the tree are flattened to a list by doing a depth-first traversal. The column metadata contains the path in the schema for that column which can be used to map columns to nodes in the schema. The first element is the root
   */
  public final java.util.List<hydra.langs.parquet.format.SchemaElement> schema;
  
  /**
   * Number of rows in this file
   */
  public final Long numRows;
  
  /**
   * Row groups in this file
   */
  public final java.util.List<hydra.langs.parquet.format.RowGroup> rowGroups;
  
  /**
   * Optional key/value metadata
   */
  public final java.util.Optional<java.util.List<hydra.langs.parquet.format.KeyValue>> keyValueMetadata;
  
  /**
   * String for application that wrote this file.  This should be in the format &lt;Application&gt; version &lt;App Version&gt; (build &lt;App Build Hash&gt;). e.g. impala version 1.0 (build 6cf94d29b2b7115df4de2c06e2ab4326d721eb55)
   */
  public final java.util.Optional<String> createdBy;
  
  /**
   * Sort order used for the min_value and max_value fields in the Statistics objects and the min_values and max_values fields in the ColumnIndex objects of each column in this file. Sort orders are listed in the order matching the columns in the schema. The indexes are not necessary the same though, because only leaf nodes of the schema are represented in the list of sort orders.
   * Without column_orders, the meaning of the min_value and max_value fields in the Statistics object and the ColumnIndex object is undefined. To ensure well-defined behaviour, if these fields are written to a Parquet file, column_orders must be written as well.
   * The obsolete min and max fields in the Statistics object are always sorted by signed comparison regardless of column_orders.
   */
  public final java.util.Optional<java.util.List<hydra.langs.parquet.format.ColumnOrder>> columnOrders;
  
  /**
   * Encryption algorithm. This field is set only in encrypted files with plaintext footer. Files with encrypted footer store algorithm id in FileCryptoMetaData structure.
   */
  public final java.util.Optional<hydra.langs.parquet.format.EncryptionAlgorithm> encryptionAlgorithm;
  
  public final java.util.Optional<String> footerSigningKeyMetadata;
  
  public FileMetaData (Integer version, java.util.List<hydra.langs.parquet.format.SchemaElement> schema, Long numRows, java.util.List<hydra.langs.parquet.format.RowGroup> rowGroups, java.util.Optional<java.util.List<hydra.langs.parquet.format.KeyValue>> keyValueMetadata, java.util.Optional<String> createdBy, java.util.Optional<java.util.List<hydra.langs.parquet.format.ColumnOrder>> columnOrders, java.util.Optional<hydra.langs.parquet.format.EncryptionAlgorithm> encryptionAlgorithm, java.util.Optional<String> footerSigningKeyMetadata) {
    this.version = version;
    this.schema = schema;
    this.numRows = numRows;
    this.rowGroups = rowGroups;
    this.keyValueMetadata = keyValueMetadata;
    this.createdBy = createdBy;
    this.columnOrders = columnOrders;
    this.encryptionAlgorithm = encryptionAlgorithm;
    this.footerSigningKeyMetadata = footerSigningKeyMetadata;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FileMetaData)) {
      return false;
    }
    FileMetaData o = (FileMetaData) (other);
    return version.equals(o.version) && schema.equals(o.schema) && numRows.equals(o.numRows) && rowGroups.equals(o.rowGroups) && keyValueMetadata.equals(o.keyValueMetadata) && createdBy.equals(o.createdBy) && columnOrders.equals(o.columnOrders) && encryptionAlgorithm.equals(o.encryptionAlgorithm) && footerSigningKeyMetadata.equals(o.footerSigningKeyMetadata);
  }
  
  @Override
  public int hashCode() {
    return 2 * version.hashCode() + 3 * schema.hashCode() + 5 * numRows.hashCode() + 7 * rowGroups.hashCode() + 11 * keyValueMetadata.hashCode() + 13 * createdBy.hashCode() + 17 * columnOrders.hashCode() + 19 * encryptionAlgorithm.hashCode() + 23 * footerSigningKeyMetadata.hashCode();
  }
  
  public FileMetaData withVersion(Integer version) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withSchema(java.util.List<hydra.langs.parquet.format.SchemaElement> schema) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withNumRows(Long numRows) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withRowGroups(java.util.List<hydra.langs.parquet.format.RowGroup> rowGroups) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withKeyValueMetadata(java.util.Optional<java.util.List<hydra.langs.parquet.format.KeyValue>> keyValueMetadata) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withCreatedBy(java.util.Optional<String> createdBy) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withColumnOrders(java.util.Optional<java.util.List<hydra.langs.parquet.format.ColumnOrder>> columnOrders) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withEncryptionAlgorithm(java.util.Optional<hydra.langs.parquet.format.EncryptionAlgorithm> encryptionAlgorithm) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
  
  public FileMetaData withFooterSigningKeyMetadata(java.util.Optional<String> footerSigningKeyMetadata) {
    return new FileMetaData(version, schema, numRows, rowGroups, keyValueMetadata, createdBy, columnOrders, encryptionAlgorithm, footerSigningKeyMetadata);
  }
}