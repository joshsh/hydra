package hydra.core;

import java.io.Serializable;

/**
 * An object wrapped in a type name
 */
public class Nominal<X> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/core.Nominal");
  
  public final hydra.core.Name typeName;
  
  public final X object;
  
  public Nominal (hydra.core.Name typeName, X object) {
    this.typeName = typeName;
    this.object = object;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Nominal)) {
      return false;
    }
    Nominal o = (Nominal) (other);
    return typeName.equals(o.typeName) && object.equals(o.object);
  }
  
  @Override
  public int hashCode() {
    return 2 * typeName.hashCode() + 3 * object.hashCode();
  }
  
  public Nominal withTypeName(hydra.core.Name typeName) {
    return new Nominal(typeName, object);
  }
  
  public Nominal withObject(X object) {
    return new Nominal(typeName, object);
  }
}