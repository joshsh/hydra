package hydra.ext.java.syntax;

public class StaticInitializer {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/java/syntax.StaticInitializer");
  
  public final hydra.ext.java.syntax.Block value;
  
  public StaticInitializer (hydra.ext.java.syntax.Block value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof StaticInitializer)) {
      return false;
    }
    StaticInitializer o = (StaticInitializer) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}