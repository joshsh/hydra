package hydra.ext.scala.meta;

public class Data_Xml {
  public final java.util.List<hydra.ext.scala.meta.Lit> parts;
  
  public final java.util.List<hydra.ext.scala.meta.Data> args;
  
  public Data_Xml (java.util.List<hydra.ext.scala.meta.Lit> parts, java.util.List<hydra.ext.scala.meta.Data> args) {
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
  
  public Data_Xml withParts(java.util.List<hydra.ext.scala.meta.Lit> parts) {
    return new Data_Xml(parts, args);
  }
  
  public Data_Xml withArgs(java.util.List<hydra.ext.scala.meta.Data> args) {
    return new Data_Xml(parts, args);
  }
}