package hydra.langs.protobuf.sourceContext;

import java.io.Serializable;

/**
 * `SourceContext` represents information about the source of a protobuf element, like the file in which it is defined.
 */
public class SourceContext implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/protobuf/sourceContext.SourceContext");
  
  /**
   * The path-qualified name of the .proto file that contained the associated protobuf element.  For example: `"google/protobuf/source_context.proto"`.
   */
  public final String fileName;
  
  public SourceContext (String fileName) {
    this.fileName = fileName;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof SourceContext)) {
      return false;
    }
    SourceContext o = (SourceContext) (other);
    return fileName.equals(o.fileName);
  }
  
  @Override
  public int hashCode() {
    return 2 * fileName.hashCode();
  }
}