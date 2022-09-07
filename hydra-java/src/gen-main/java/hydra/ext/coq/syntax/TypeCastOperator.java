package hydra.ext.coq.syntax;

public abstract class TypeCastOperator {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/coq/syntax.TypeCastOperator");
  
  private TypeCastOperator () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Normal instance) ;
    
    R visit(VmCompute instance) ;
    
    R visit(NativeCompute instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(TypeCastOperator instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Normal instance) {
      return otherwise((instance));
    }
    
    default R visit(VmCompute instance) {
      return otherwise((instance));
    }
    
    default R visit(NativeCompute instance) {
      return otherwise((instance));
    }
  }
  
  /**
   * The expression term10 : type is a type cast expression. It enforces the type of term10 to be type.
   */
  public static final class Normal extends hydra.ext.coq.syntax.TypeCastOperator {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/coq/syntax.Normal");
    
    public Normal () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Normal)) {
        return false;
      }
      Normal o = (Normal) (other);
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
  
  /**
   * term10 <: type specifies that the virtual machine will be used to type check that term10 has type type (see vm_compute).
   */
  public static final class VmCompute extends hydra.ext.coq.syntax.TypeCastOperator {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/coq/syntax.VmCompute");
    
    public VmCompute () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof VmCompute)) {
        return false;
      }
      VmCompute o = (VmCompute) (other);
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
  
  /**
   * term10 <<: type specifies that compilation to OCaml will be used to type check that term10 has type type (see native_compute).
   */
  public static final class NativeCompute extends hydra.ext.coq.syntax.TypeCastOperator {
    public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/coq/syntax.NativeCompute");
    
    public NativeCompute () {
    
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof NativeCompute)) {
        return false;
      }
      NativeCompute o = (NativeCompute) (other);
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