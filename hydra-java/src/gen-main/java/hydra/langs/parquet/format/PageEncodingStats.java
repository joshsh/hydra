package hydra.langs.parquet.format;

import java.io.Serializable;

/**
 * statistics of a given page type and encoding
 */
public class PageEncodingStats implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.PageEncodingStats");
  
  /**
   * the page type (data/dic/...)
   */
  public final hydra.langs.parquet.format.PageType pageType;
  
  /**
   * encoding of the page
   */
  public final hydra.langs.parquet.format.Encoding encoding;
  
  /**
   * number of pages of this type with this encoding
   */
  public final Integer count;
  
  public PageEncodingStats (hydra.langs.parquet.format.PageType pageType, hydra.langs.parquet.format.Encoding encoding, Integer count) {
    this.pageType = pageType;
    this.encoding = encoding;
    this.count = count;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof PageEncodingStats)) {
      return false;
    }
    PageEncodingStats o = (PageEncodingStats) (other);
    return pageType.equals(o.pageType) && encoding.equals(o.encoding) && count.equals(o.count);
  }
  
  @Override
  public int hashCode() {
    return 2 * pageType.hashCode() + 3 * encoding.hashCode() + 5 * count.hashCode();
  }
  
  public PageEncodingStats withPageType(hydra.langs.parquet.format.PageType pageType) {
    return new PageEncodingStats(pageType, encoding, count);
  }
  
  public PageEncodingStats withEncoding(hydra.langs.parquet.format.Encoding encoding) {
    return new PageEncodingStats(pageType, encoding, count);
  }
  
  public PageEncodingStats withCount(Integer count) {
    return new PageEncodingStats(pageType, encoding, count);
  }
}