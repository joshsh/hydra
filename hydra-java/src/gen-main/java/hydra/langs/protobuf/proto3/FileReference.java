package hydra.langs.protobuf.proto3;

import java.io.Serializable;

public class FileReference implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/proto3.FileReference");
  
  public final String value;
  
  public FileReference (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof FileReference)) {
      return false;
    }
    FileReference o = (FileReference) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}