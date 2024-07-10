// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Type_Annotate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Type.Annotate");
  
  public final hydra.langs.scala.meta.Type tpe;
  
  public final java.util.List<hydra.langs.scala.meta.Mod_Annot> annots;
  
  public Type_Annotate (hydra.langs.scala.meta.Type tpe, java.util.List<hydra.langs.scala.meta.Mod_Annot> annots) {
    if (tpe == null) {
      throw new IllegalArgumentException("null value for 'tpe' argument");
    }
    if (annots == null) {
      throw new IllegalArgumentException("null value for 'annots' argument");
    }
    this.tpe = tpe;
    this.annots = annots;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Annotate)) {
      return false;
    }
    Type_Annotate o = (Type_Annotate) (other);
    return tpe.equals(o.tpe) && annots.equals(o.annots);
  }
  
  @Override
  public int hashCode() {
    return 2 * tpe.hashCode() + 3 * annots.hashCode();
  }
  
  public Type_Annotate withTpe(hydra.langs.scala.meta.Type tpe) {
    if (tpe == null) {
      throw new IllegalArgumentException("null value for 'tpe' argument");
    }
    return new Type_Annotate(tpe, annots);
  }
  
  public Type_Annotate withAnnots(java.util.List<hydra.langs.scala.meta.Mod_Annot> annots) {
    if (annots == null) {
      throw new IllegalArgumentException("null value for 'annots' argument");
    }
    return new Type_Annotate(tpe, annots);
  }
}