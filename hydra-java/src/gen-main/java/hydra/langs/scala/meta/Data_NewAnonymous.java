// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_NewAnonymous implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.NewAnonymous");
  
  public final hydra.langs.scala.meta.Template templ;
  
  public Data_NewAnonymous (hydra.langs.scala.meta.Template templ) {
    if (templ == null) {
      throw new IllegalArgumentException("null value for 'templ' argument");
    }
    this.templ = templ;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_NewAnonymous)) {
      return false;
    }
    Data_NewAnonymous o = (Data_NewAnonymous) (other);
    return templ.equals(o.templ);
  }
  
  @Override
  public int hashCode() {
    return 2 * templ.hashCode();
  }
}