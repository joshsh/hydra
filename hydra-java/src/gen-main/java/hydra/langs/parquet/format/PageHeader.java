package hydra.langs.parquet.format;

import java.io.Serializable;

public class PageHeader implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.PageHeader");
  
  /**
   * the type of the page: indicates which of the *_header fields is set
   */
  public final hydra.langs.parquet.format.PageType type;
  
  /**
   * Uncompressed page size in bytes (not including this header)
   */
  public final Integer uncompressedPageSize;
  
  /**
   * Compressed (and potentially encrypted) page size in bytes, not including this header
   */
  public final Integer compressedPageSize;
  
  /**
   * The 32bit CRC for the page, to be be calculated as follows:
   * - Using the standard CRC32 algorithm
   * - On the data only, i.e. this header should not be included. 'Data'
   *   hereby refers to the concatenation of the repetition levels, the
   *   definition levels and the column value, in this exact order.
   * - On the encoded versions of the repetition levels, definition levels and
   *   column values
   * - On the compressed versions of the repetition levels, definition levels
   *   and column values where possible;
   *   - For v1 data pages, the repetition levels, definition levels and column
   *     values are always compressed together. If a compression scheme is
   *     specified, the CRC shall be calculated on the compressed version of
   *     this concatenation. If no compression scheme is specified, the CRC
   *     shall be calculated on the uncompressed version of this concatenation.
   *   - For v2 data pages, the repetition levels and definition levels are
   *     handled separately from the data and are never compressed (only
   *     encoded). If a compression scheme is specified, the CRC shall be
   *     calculated on the concatenation of the uncompressed repetition levels,
   *     uncompressed definition levels and the compressed column values.
   *     If no compression scheme is specified, the CRC shall be calculated on
   *     the uncompressed concatenation.
   * - In encrypted columns, CRC is calculated after page encryption; the
   *   encryption itself is performed after page compression (if compressed)
   * If enabled, this allows for disabling checksumming in HDFS if only a few pages need to be read. 
   */
  public final java.util.Optional<Integer> crc;
  
  public final java.util.Optional<hydra.langs.parquet.format.DataPageHeader> dataPageHeader;
  
  public final java.util.Optional<hydra.langs.parquet.format.IndexPageHeader> indexPageHeader;
  
  public final java.util.Optional<hydra.langs.parquet.format.DictionaryPageHeader> dictionaryPageHeader;
  
  public final java.util.Optional<hydra.langs.parquet.format.DataPageHeaderV2> dataPageHeaderV2;
  
  public PageHeader (hydra.langs.parquet.format.PageType type, Integer uncompressedPageSize, Integer compressedPageSize, java.util.Optional<Integer> crc, java.util.Optional<hydra.langs.parquet.format.DataPageHeader> dataPageHeader, java.util.Optional<hydra.langs.parquet.format.IndexPageHeader> indexPageHeader, java.util.Optional<hydra.langs.parquet.format.DictionaryPageHeader> dictionaryPageHeader, java.util.Optional<hydra.langs.parquet.format.DataPageHeaderV2> dataPageHeaderV2) {
    this.type = type;
    this.uncompressedPageSize = uncompressedPageSize;
    this.compressedPageSize = compressedPageSize;
    this.crc = crc;
    this.dataPageHeader = dataPageHeader;
    this.indexPageHeader = indexPageHeader;
    this.dictionaryPageHeader = dictionaryPageHeader;
    this.dataPageHeaderV2 = dataPageHeaderV2;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PageHeader)) {
      return false;
    }
    PageHeader o = (PageHeader) (other);
    return type.equals(o.type) && uncompressedPageSize.equals(o.uncompressedPageSize) && compressedPageSize.equals(o.compressedPageSize) && crc.equals(o.crc) && dataPageHeader.equals(o.dataPageHeader) && indexPageHeader.equals(o.indexPageHeader) && dictionaryPageHeader.equals(o.dictionaryPageHeader) && dataPageHeaderV2.equals(o.dataPageHeaderV2);
  }
  
  @Override
  public int hashCode() {
    return 2 * type.hashCode() + 3 * uncompressedPageSize.hashCode() + 5 * compressedPageSize.hashCode() + 7 * crc.hashCode() + 11 * dataPageHeader.hashCode() + 13 * indexPageHeader.hashCode() + 17 * dictionaryPageHeader.hashCode() + 19 * dataPageHeaderV2.hashCode();
  }
  
  public PageHeader withType(hydra.langs.parquet.format.PageType type) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
  
  public PageHeader withUncompressedPageSize(Integer uncompressedPageSize) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
  
  public PageHeader withCompressedPageSize(Integer compressedPageSize) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
  
  public PageHeader withCrc(java.util.Optional<Integer> crc) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
  
  public PageHeader withDataPageHeader(java.util.Optional<hydra.langs.parquet.format.DataPageHeader> dataPageHeader) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
  
  public PageHeader withIndexPageHeader(java.util.Optional<hydra.langs.parquet.format.IndexPageHeader> indexPageHeader) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
  
  public PageHeader withDictionaryPageHeader(java.util.Optional<hydra.langs.parquet.format.DictionaryPageHeader> dictionaryPageHeader) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
  
  public PageHeader withDataPageHeaderV2(java.util.Optional<hydra.langs.parquet.format.DataPageHeaderV2> dataPageHeaderV2) {
    return new PageHeader(type, uncompressedPageSize, compressedPageSize, crc, dataPageHeader, indexPageHeader, dictionaryPageHeader, dataPageHeaderV2);
  }
}