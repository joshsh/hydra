package hydra.langs.scala.meta;

import java.io.Serializable;

public class ScalaSymbol implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.ScalaSymbol");
  
  public final String name;
  
  public ScalaSymbol (String name) {
    this.name = name;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ScalaSymbol)) {
      return false;
    }
    ScalaSymbol o = (ScalaSymbol) (other);
    return name.equals(o.name);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode();
  }
}