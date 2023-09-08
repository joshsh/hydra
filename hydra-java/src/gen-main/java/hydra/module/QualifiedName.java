package hydra.module;

import java.io.Serializable;

/**
 * A qualified name consisting of an optional namespace together with a mandatory local name
 */
public class QualifiedName implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/module.QualifiedName");
  
  public final java.util.Optional<hydra.module.Namespace> namespace;
  
  public final String local;
  
  public QualifiedName (java.util.Optional<hydra.module.Namespace> namespace, String local) {
    this.namespace = namespace;
    this.local = local;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof QualifiedName)) {
      return false;
    }
    QualifiedName o = (QualifiedName) (other);
    return namespace.equals(o.namespace) && local.equals(o.local);
  }
  
  @Override
  public int hashCode() {
    return 2 * namespace.hashCode() + 3 * local.hashCode();
  }
  
  public QualifiedName withNamespace(java.util.Optional<hydra.module.Namespace> namespace) {
    return new QualifiedName(namespace, local);
  }
  
  public QualifiedName withLocal(String local) {
    return new QualifiedName(namespace, local);
  }
}