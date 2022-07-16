package hydra.ext.tinkerpop.features;

/**
 * Additional features which are needed for the complete specification of language constraints in Hydra, above and beyond TinkerPop Graph.Features
 */
public class ExtraFeatures<M> {
  public final java.util.function.Function<hydra.core.Type<M>, Boolean> supportsMapKey;
  
  public ExtraFeatures (java.util.function.Function<hydra.core.Type<M>, Boolean> supportsMapKey) {
    this.supportsMapKey = supportsMapKey;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ExtraFeatures)) {
      return false;
    }
    ExtraFeatures o = (ExtraFeatures) (other);
    return supportsMapKey.equals(o.supportsMapKey);
  }
  
  @Override
  public int hashCode() {
    return 2 * supportsMapKey.hashCode();
  }
}