// Note: this is an automatically generated file. Do not edit.

package hydra.module;

import java.io.Serializable;

/**
 * A file extension (without the dot), e.g. "json" or "py"
 */
public class FileExtension implements Serializable {
  public static final hydra.core.Name TYPE_NAME = new hydra.core.Name("hydra/module.FileExtension");
  
  public static final hydra.core.Name FIELD_NAME_VALUE = new hydra.core.Name("value");
  
  public final String value;
  
  public FileExtension (String value) {
    java.util.Objects.requireNonNull((value));
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FileExtension)) {
      return false;
    }
    FileExtension o = (FileExtension) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}