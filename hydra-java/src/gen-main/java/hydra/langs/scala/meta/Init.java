package hydra.langs.scala.meta;

import java.io.Serializable;

public class Init implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Init");
  
  public final hydra.langs.scala.meta.Type tpe;
  
  public final hydra.langs.scala.meta.Name name;
  
  public final java.util.List<java.util.List<hydra.langs.scala.meta.Data>> argss;
  
  public Init (hydra.langs.scala.meta.Type tpe, hydra.langs.scala.meta.Name name, java.util.List<java.util.List<hydra.langs.scala.meta.Data>> argss) {
    this.tpe = tpe;
    this.name = name;
    this.argss = argss;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Init)) {
      return false;
    }
    Init o = (Init) (other);
    return tpe.equals(o.tpe) && name.equals(o.name) && argss.equals(o.argss);
  }
  
  @Override
  public int hashCode() {
    return 2 * tpe.hashCode() + 3 * name.hashCode() + 5 * argss.hashCode();
  }
  
  public Init withTpe(hydra.langs.scala.meta.Type tpe) {
    return new Init(tpe, name, argss);
  }
  
  public Init withName(hydra.langs.scala.meta.Name name) {
    return new Init(tpe, name, argss);
  }
  
  public Init withArgss(java.util.List<java.util.List<hydra.langs.scala.meta.Data>> argss) {
    return new Init(tpe, name, argss);
  }
}