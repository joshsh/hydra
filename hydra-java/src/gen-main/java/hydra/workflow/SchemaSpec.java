package hydra.workflow;

import java.io.Serializable;

/**
 * The specification of a schema at the source end of a workflow
 */
public abstract class SchemaSpec implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/workflow.SchemaSpec");
  
  private SchemaSpec () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Hydra instance) ;
    
    R visit(File instance) ;
    
    R visit(Provided instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(SchemaSpec instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Hydra instance) {
      return otherwise((instance));
    }
    
    default R visit(File instance) {
      return otherwise((instance));
    }
    
    default R visit(Provided instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * A native Hydra schema
   */
  public static final class Hydra extends hydra.workflow.SchemaSpec implements Serializable {
    /**
     * A native Hydra schema
     */
    public final hydra.workflow.HydraSchemaSpec value;
    
    public Hydra (hydra.workflow.HydraSchemaSpec value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Hydra)) {
        return false;
      }
      Hydra o = (Hydra) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
  
  /**
   * A schema provided as a file, available at the given file path
   */
  public static final class File extends hydra.workflow.SchemaSpec implements Serializable {
    /**
     * A schema provided as a file, available at the given file path
     */
    public final String value;
    
    public File (String value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof File)) {
        return false;
      }
      File o = (File) (other);
      return value.equals(o.value);
    }
    
    @Override
    public int hashCode() {
      return 2 * value.hashCode();
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
  
  /**
   * A schema which will be provided within the workflow
   */
  public static final class Provided extends hydra.workflow.SchemaSpec implements Serializable {
    public Provided () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Provided)) {
        return false;
      }
      Provided o = (Provided) (other);
      return true;
    }
    
    @Override
    public int hashCode() {
      return 0;
    }
    
    @Override
    public <R> R accept(Visitor<R> visitor) {
      return visitor.visit(this);
    }
  }
}