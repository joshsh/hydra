package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Annotate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Annotate");
  
  public final hydra.langs.scala.meta.Data expr;
  
  public final java.util.List<hydra.langs.scala.meta.Mod_Annot> annots;
  
  public Data_Annotate (hydra.langs.scala.meta.Data expr, java.util.List<hydra.langs.scala.meta.Mod_Annot> annots) {
    this.expr = expr;
    this.annots = annots;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Annotate)) {
      return false;
    }
    Data_Annotate o = (Data_Annotate) (other);
    return expr.equals(o.expr) && annots.equals(o.annots);
  }
  
  @Override
  public int hashCode() {
    return 2 * expr.hashCode() + 3 * annots.hashCode();
  }
  
  public Data_Annotate withExpr(hydra.langs.scala.meta.Data expr) {
    return new Data_Annotate(expr, annots);
  }
  
  public Data_Annotate withAnnots(java.util.List<hydra.langs.scala.meta.Mod_Annot> annots) {
    return new Data_Annotate(expr, annots);
  }
}