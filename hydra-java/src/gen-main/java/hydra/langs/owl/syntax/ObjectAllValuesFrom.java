package hydra.langs.owl.syntax;

import java.io.Serializable;

public class ObjectAllValuesFrom implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.ObjectAllValuesFrom");
  
  public final hydra.langs.owl.syntax.ObjectPropertyExpression property;
  
  public final hydra.langs.owl.syntax.ClassExpression class_;
  
  public ObjectAllValuesFrom (hydra.langs.owl.syntax.ObjectPropertyExpression property, hydra.langs.owl.syntax.ClassExpression class_) {
    this.property = property;
    this.class_ = class_;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ObjectAllValuesFrom)) {
      return false;
    }
    ObjectAllValuesFrom o = (ObjectAllValuesFrom) (other);
    return property.equals(o.property) && class_.equals(o.class_);
  }
  
  @Override
  public int hashCode() {
    return 2 * property.hashCode() + 3 * class_.hashCode();
  }
  
  public ObjectAllValuesFrom withProperty(hydra.langs.owl.syntax.ObjectPropertyExpression property) {
    return new ObjectAllValuesFrom(property, class_);
  }
  
  public ObjectAllValuesFrom withClass(hydra.langs.owl.syntax.ClassExpression class_) {
    return new ObjectAllValuesFrom(property, class_);
  }
}