package hydra.langs.rdf.syntax;

import java.io.Serializable;

/**
 * Stand-in for rdfs:Class
 */
public class RdfsClass implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/rdf/syntax.RdfsClass");
  
  public RdfsClass () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof RdfsClass)) {
      return false;
    }
    RdfsClass o = (RdfsClass) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}