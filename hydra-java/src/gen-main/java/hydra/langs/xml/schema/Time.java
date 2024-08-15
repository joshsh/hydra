// Note: this is an automatically generated file. Do not edit.

package hydra.langs.xml.schema;

import java.io.Serializable;

public class Time implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/langs/xml/schema.Time");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final String value;
  
  public Time (String value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Time)) {
      return false;
    }
    Time o = (Time) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}