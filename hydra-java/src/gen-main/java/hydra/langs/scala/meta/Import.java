package hydra.langs.scala.meta;

import java.io.Serializable;

public class Import implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Import");
  
  public final java.util.List<hydra.langs.scala.meta.Importer> importers;
  
  public Import (java.util.List<hydra.langs.scala.meta.Importer> importers) {
    this.importers = importers;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Import)) {
      return false;
    }
    Import o = (Import) (other);
    return importers.equals(o.importers);
  }
  
  @Override
  public int hashCode() {
    return 2 * importers.hashCode();
  }
}