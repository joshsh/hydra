package hydra.langs.pegasus.pdl;

import java.io.Serializable;

public class UnionMember implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/pegasus/pdl.UnionMember");
  
  public final java.util.Optional<hydra.langs.pegasus.pdl.FieldName> alias;
  
  public final hydra.langs.pegasus.pdl.Schema value;
  
  public final hydra.langs.pegasus.pdl.Annotations annotations;
  
  public UnionMember (java.util.Optional<hydra.langs.pegasus.pdl.FieldName> alias, hydra.langs.pegasus.pdl.Schema value, hydra.langs.pegasus.pdl.Annotations annotations) {
    this.alias = alias;
    this.value = value;
    this.annotations = annotations;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof UnionMember)) {
      return false;
    }
    UnionMember o = (UnionMember) (other);
    return alias.equals(o.alias) && value.equals(o.value) && annotations.equals(o.annotations);
  }
  
  @Override
  public int hashCode() {
    return 2 * alias.hashCode() + 3 * value.hashCode() + 5 * annotations.hashCode();
  }
  
  public UnionMember withAlias(java.util.Optional<hydra.langs.pegasus.pdl.FieldName> alias) {
    return new UnionMember(alias, value, annotations);
  }
  
  public UnionMember withValue(hydra.langs.pegasus.pdl.Schema value) {
    return new UnionMember(alias, value, annotations);
  }
  
  public UnionMember withAnnotations(hydra.langs.pegasus.pdl.Annotations annotations) {
    return new UnionMember(alias, value, annotations);
  }
}