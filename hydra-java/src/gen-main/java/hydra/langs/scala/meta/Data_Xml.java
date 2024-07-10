// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Data_Xml implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Data.Xml");
  
  public final java.util.List<hydra.langs.scala.meta.Lit> parts;
  
  public final java.util.List<hydra.langs.scala.meta.Data> args;
  
  public Data_Xml (java.util.List<hydra.langs.scala.meta.Lit> parts, java.util.List<hydra.langs.scala.meta.Data> args) {
    if (parts == null) {
      throw new IllegalArgumentException("null value for 'parts' argument");
    }
    if (args == null) {
      throw new IllegalArgumentException("null value for 'args' argument");
    }
    this.parts = parts;
    this.args = args;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Xml)) {
      return false;
    }
    Data_Xml o = (Data_Xml) (other);
    return parts.equals(o.parts) && args.equals(o.args);
  }
  
  @Override
  public int hashCode() {
    return 2 * parts.hashCode() + 3 * args.hashCode();
  }
  
  public Data_Xml withParts(java.util.List<hydra.langs.scala.meta.Lit> parts) {
    if (parts == null) {
      throw new IllegalArgumentException("null value for 'parts' argument");
    }
    return new Data_Xml(parts, args);
  }
  
  public Data_Xml withArgs(java.util.List<hydra.langs.scala.meta.Data> args) {
    if (args == null) {
      throw new IllegalArgumentException("null value for 'args' argument");
    }
    return new Data_Xml(parts, args);
  }
}