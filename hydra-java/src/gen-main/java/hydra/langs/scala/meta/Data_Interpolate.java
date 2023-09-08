package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Interpolate implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Interpolate");
  
  public final hydra.langs.scala.meta.Data_Name prefix;
  
  public final java.util.List<hydra.langs.scala.meta.Lit> parts;
  
  public final java.util.List<hydra.langs.scala.meta.Data> args;
  
  public Data_Interpolate (hydra.langs.scala.meta.Data_Name prefix, java.util.List<hydra.langs.scala.meta.Lit> parts, java.util.List<hydra.langs.scala.meta.Data> args) {
    this.prefix = prefix;
    this.parts = parts;
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Interpolate)) {
      return false;
    }
    Data_Interpolate o = (Data_Interpolate) (other);
    return prefix.equals(o.prefix) && parts.equals(o.parts) && args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * prefix.hashCode() + 3 * parts.hashCode() + 5 * args.hashCode();
  }
  
  public Data_Interpolate withPrefix(hydra.langs.scala.meta.Data_Name prefix) {
    return new Data_Interpolate(prefix, parts, args);
  }
  
  public Data_Interpolate withParts(java.util.List<hydra.langs.scala.meta.Lit> parts) {
    return new Data_Interpolate(prefix, parts, args);
  }
  
  public Data_Interpolate withArgs(java.util.List<hydra.langs.scala.meta.Data> args) {
    return new Data_Interpolate(prefix, parts, args);
  }
}