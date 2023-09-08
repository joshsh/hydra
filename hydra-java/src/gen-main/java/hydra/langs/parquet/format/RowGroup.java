package hydra.langs.parquet.format;

import java.io.Serializable;

public class RowGroup implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.RowGroup");
  
  /**
   * Metadata for each column chunk in this row group. This list must have the same order as the SchemaElement list in FileMetaData.
   */
  public final java.util.List<hydra.langs.parquet.format.ColumnChunk> columns;
  
  /**
   * Total byte size of all the uncompressed column data in this row group
   */
  public final Long totalByteSize;
  
  /**
   * Number of rows in this row group
   */
  public final Long numRows;
  
  /**
   * If set, specifies a sort ordering of the rows in this RowGroup. The sorting columns can be a subset of all the columns.
   */
  public final java.util.Optional<java.util.List<hydra.langs.parquet.format.SortingColumn>> sortingColumns;
  
  /**
   * Byte offset from beginning of file to first page (data or dictionary) in this row group
   */
  public final java.util.Optional<Long> fileOffset;
  
  /**
   * Total byte size of all compressed (and potentially encrypted) column data in this row group
   */
  public final java.util.Optional<Long> totalCompressedSize;
  
  /**
   * Row group ordinal in the file
   */
  public final java.util.Optional<Short> ordinal;
  
  public RowGroup (java.util.List<hydra.langs.parquet.format.ColumnChunk> columns, Long totalByteSize, Long numRows, java.util.Optional<java.util.List<hydra.langs.parquet.format.SortingColumn>> sortingColumns, java.util.Optional<Long> fileOffset, java.util.Optional<Long> totalCompressedSize, java.util.Optional<Short> ordinal) {
    this.columns = columns;
    this.totalByteSize = totalByteSize;
    this.numRows = numRows;
    this.sortingColumns = sortingColumns;
    this.fileOffset = fileOffset;
    this.totalCompressedSize = totalCompressedSize;
    this.ordinal = ordinal;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RowGroup)) {
      return false;
    }
    RowGroup o = (RowGroup) (other);
    return columns.equals(o.columns) && totalByteSize.equals(o.totalByteSize) && numRows.equals(o.numRows) && sortingColumns.equals(o.sortingColumns) && fileOffset.equals(o.fileOffset) && totalCompressedSize.equals(o.totalCompressedSize) && ordinal.equals(o.ordinal);
  }
  
  @Override
  public int hashCode() {
    return 2 * columns.hashCode() + 3 * totalByteSize.hashCode() + 5 * numRows.hashCode() + 7 * sortingColumns.hashCode() + 11 * fileOffset.hashCode() + 13 * totalCompressedSize.hashCode() + 17 * ordinal.hashCode();
  }
  
  public RowGroup withColumns(java.util.List<hydra.langs.parquet.format.ColumnChunk> columns) {
    return new RowGroup(columns, totalByteSize, numRows, sortingColumns, fileOffset, totalCompressedSize, ordinal);
  }
  
  public RowGroup withTotalByteSize(Long totalByteSize) {
    return new RowGroup(columns, totalByteSize, numRows, sortingColumns, fileOffset, totalCompressedSize, ordinal);
  }
  
  public RowGroup withNumRows(Long numRows) {
    return new RowGroup(columns, totalByteSize, numRows, sortingColumns, fileOffset, totalCompressedSize, ordinal);
  }
  
  public RowGroup withSortingColumns(java.util.Optional<java.util.List<hydra.langs.parquet.format.SortingColumn>> sortingColumns) {
    return new RowGroup(columns, totalByteSize, numRows, sortingColumns, fileOffset, totalCompressedSize, ordinal);
  }
  
  public RowGroup withFileOffset(java.util.Optional<Long> fileOffset) {
    return new RowGroup(columns, totalByteSize, numRows, sortingColumns, fileOffset, totalCompressedSize, ordinal);
  }
  
  public RowGroup withTotalCompressedSize(java.util.Optional<Long> totalCompressedSize) {
    return new RowGroup(columns, totalByteSize, numRows, sortingColumns, fileOffset, totalCompressedSize, ordinal);
  }
  
  public RowGroup withOrdinal(java.util.Optional<Short> ordinal) {
    return new RowGroup(columns, totalByteSize, numRows, sortingColumns, fileOffset, totalCompressedSize, ordinal);
  }
}