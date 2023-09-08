package hydra.workflow;

import java.io.Serializable;

/**
 * The specification of a workflow which takes a schema specification, reads data from a directory, and writes data to another directory
 */
public class TransformWorkflow implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/workflow.TransformWorkflow");
  
  /**
   * A descriptive name for the workflow
   */
  public final String name;
  
  /**
   * The schema specification
   */
  public final hydra.workflow.SchemaSpec schemaSpec;
  
  /**
   * The source directory
   */
  public final String srcDir;
  
  /**
   * The destination directory
   */
  public final String destDir;
  
  public TransformWorkflow (String name, hydra.workflow.SchemaSpec schemaSpec, String srcDir, String destDir) {
    this.name = name;
    this.schemaSpec = schemaSpec;
    this.srcDir = srcDir;
    this.destDir = destDir;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TransformWorkflow)) {
      return false;
    }
    TransformWorkflow o = (TransformWorkflow) (other);
    return name.equals(o.name) && schemaSpec.equals(o.schemaSpec) && srcDir.equals(o.srcDir) && destDir.equals(o.destDir);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * schemaSpec.hashCode() + 5 * srcDir.hashCode() + 7 * destDir.hashCode();
  }
  
  public TransformWorkflow withName(String name) {
    return new TransformWorkflow(name, schemaSpec, srcDir, destDir);
  }
  
  public TransformWorkflow withSchemaSpec(hydra.workflow.SchemaSpec schemaSpec) {
    return new TransformWorkflow(name, schemaSpec, srcDir, destDir);
  }
  
  public TransformWorkflow withSrcDir(String srcDir) {
    return new TransformWorkflow(name, schemaSpec, srcDir, destDir);
  }
  
  public TransformWorkflow withDestDir(String destDir) {
    return new TransformWorkflow(name, schemaSpec, srcDir, destDir);
  }
}