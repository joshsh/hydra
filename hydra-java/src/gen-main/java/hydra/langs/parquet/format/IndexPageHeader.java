package hydra.langs.parquet.format;

import java.io.Serializable;

public class IndexPageHeader implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/parquet/format.IndexPageHeader");
  
  public IndexPageHeader () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof IndexPageHeader)) {
      return false;
    }
    IndexPageHeader o = (IndexPageHeader) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}