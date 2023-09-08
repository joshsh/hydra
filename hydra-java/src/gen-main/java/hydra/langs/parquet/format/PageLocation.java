package hydra.langs.parquet.format;

import java.io.Serializable;

public class PageLocation implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.PageLocation");
  
  /**
   * Offset of the page in the file
   */
  public final Long offset;
  
  /**
   * Size of the page, including header. Sum of compressed_page_size and header length
   */
  public final Integer compressedPageSize;
  
  /**
   * Index within the RowGroup of the first row of the page; this means pages change on record boundaries (r = 0).
   */
  public final Long firstRowIndex;
  
  public PageLocation (Long offset, Integer compressedPageSize, Long firstRowIndex) {
    this.offset = offset;
    this.compressedPageSize = compressedPageSize;
    this.firstRowIndex = firstRowIndex;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PageLocation)) {
      return false;
    }
    PageLocation o = (PageLocation) (other);
    return offset.equals(o.offset) && compressedPageSize.equals(o.compressedPageSize) && firstRowIndex.equals(o.firstRowIndex);
  }
  
  @Override
  public int hashCode() {
    return 2 * offset.hashCode() + 3 * compressedPageSize.hashCode() + 5 * firstRowIndex.hashCode();
  }
  
  public PageLocation withOffset(Long offset) {
    return new PageLocation(offset, compressedPageSize, firstRowIndex);
  }
  
  public PageLocation withCompressedPageSize(Integer compressedPageSize) {
    return new PageLocation(offset, compressedPageSize, firstRowIndex);
  }
  
  public PageLocation withFirstRowIndex(Long firstRowIndex) {
    return new PageLocation(offset, compressedPageSize, firstRowIndex);
  }
}