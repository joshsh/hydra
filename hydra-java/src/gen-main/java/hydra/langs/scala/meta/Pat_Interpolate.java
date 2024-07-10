// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Pat_Interpolate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Pat.Interpolate");
  
  public final hydra.langs.scala.meta.Data_Name prefix;
  
  public final java.util.List<hydra.langs.scala.meta.Lit> parts;
  
  public Pat_Interpolate (hydra.langs.scala.meta.Data_Name prefix, java.util.List<hydra.langs.scala.meta.Lit> parts) {
    if (prefix == null) {
      throw new IllegalArgumentException("null value for 'prefix' argument");
    }
    if (parts == null) {
      throw new IllegalArgumentException("null value for 'parts' argument");
    }
    this.prefix = prefix;
    this.parts = parts;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Pat_Interpolate)) {
      return false;
    }
    Pat_Interpolate o = (Pat_Interpolate) (other);
    return prefix.equals(o.prefix) && parts.equals(o.parts);
  }
  
  @Override
  public int hashCode() {
    return 2 * prefix.hashCode() + 3 * parts.hashCode();
  }
  
  public Pat_Interpolate withPrefix(hydra.langs.scala.meta.Data_Name prefix) {
    if (prefix == null) {
      throw new IllegalArgumentException("null value for 'prefix' argument");
    }
    return new Pat_Interpolate(prefix, parts);
  }
  
  public Pat_Interpolate withParts(java.util.List<hydra.langs.scala.meta.Lit> parts) {
    if (parts == null) {
      throw new IllegalArgumentException("null value for 'parts' argument");
    }
    return new Pat_Interpolate(prefix, parts);
  }
}