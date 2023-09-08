package hydra.module;

import java.io.Serializable;

public class FileExtension implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/module.FileExtension");
  
  public final String value;
  
  public FileExtension (String value) {
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