// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Export implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Export");
  
  public final java.util.List<hydra.langs.scala.meta.Importer> importers;
  
  public Export (java.util.List<hydra.langs.scala.meta.Importer> importers) {
    if (importers == null) {
      throw new IllegalArgumentException("null value for 'importers' argument");
    }
    this.importers = importers;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Export)) {
      return false;
    }
    Export o = (Export) (other);
    return importers.equals(o.importers);
  }
  
  @Override
  public int hashCode() {
    return 2 * importers.hashCode();
  }
}