package hydra.ext.java.syntax;

public class StaticInitializer {
  public final Block value;
  
  public StaticInitializer (Block value) {
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