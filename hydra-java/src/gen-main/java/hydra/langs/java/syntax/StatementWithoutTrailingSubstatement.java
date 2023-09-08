package hydra.langs.java.syntax;

import java.io.Serializable;

public abstract class StatementWithoutTrailingSubstatement implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/java/syntax.StatementWithoutTrailingSubstatement");
  
  private StatementWithoutTrailingSubstatement () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Block instance) ;
    
    R visit(Empty instance) ;
    
    R visit(Expression instance) ;
    
    R visit(Assert instance) ;
    
    R visit(Switch instance) ;
    
    R visit(Do instance) ;
    
    R visit(Break instance) ;
    
    R visit(Continue instance) ;
    
    R visit(Return instance) ;
    
    R visit(Synchronized instance) ;
    
    R visit(Throw instance) ;
    
    R visit(Try instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(StatementWithoutTrailingSubstatement instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Block instance) {
      return otherwise((instance));
    }
    
    default R visit(Empty instance) {
      return otherwise((instance));
    }
    
    default R visit(Expression instance) {
      return otherwise((instance));
    }
    
    default R visit(Assert instance) {
      return otherwise((instance));
    }
    
    default R visit(Switch instance) {
      return otherwise((instance));
    }
    
    default R visit(Do instance) {
      return otherwise((instance));
    }
    
    default R visit(Break instance) {
      return otherwise((instance));
    }
    
    default R visit(Continue instance) {
      return otherwise((instance));
    }
    
    default R visit(Return instance) {
      return otherwise((instance));
    }
    
    default R visit(Synchronized instance) {
      return otherwise((instance));
    }
    
    default R visit(Throw instance) {
      return otherwise((instance));
    }
    
    default R visit(Try instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Block extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.Block value;
    
    public Block (hydra.langs.java.syntax.Block value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Block)) {
        return false;
      }
      Block o = (Block) (other);
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
  
  public static final class Empty extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.EmptyStatement value;
    
    public Empty (hydra.langs.java.syntax.EmptyStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Empty)) {
        return false;
      }
      Empty o = (Empty) (other);
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
  
  public static final class Expression extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.ExpressionStatement value;
    
    public Expression (hydra.langs.java.syntax.ExpressionStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Expression)) {
        return false;
      }
      Expression o = (Expression) (other);
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
  
  public static final class Assert extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.AssertStatement value;
    
    public Assert (hydra.langs.java.syntax.AssertStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Assert)) {
        return false;
      }
      Assert o = (Assert) (other);
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
  
  public static final class Switch extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.SwitchStatement value;
    
    public Switch (hydra.langs.java.syntax.SwitchStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Switch)) {
        return false;
      }
      Switch o = (Switch) (other);
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
  
  public static final class Do extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.DoStatement value;
    
    public Do (hydra.langs.java.syntax.DoStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Do)) {
        return false;
      }
      Do o = (Do) (other);
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
  
  public static final class Break extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.BreakStatement value;
    
    public Break (hydra.langs.java.syntax.BreakStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Break)) {
        return false;
      }
      Break o = (Break) (other);
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
  
  public static final class Continue extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.ContinueStatement value;
    
    public Continue (hydra.langs.java.syntax.ContinueStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Continue)) {
        return false;
      }
      Continue o = (Continue) (other);
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
  
  public static final class Return extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.ReturnStatement value;
    
    public Return (hydra.langs.java.syntax.ReturnStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Return)) {
        return false;
      }
      Return o = (Return) (other);
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
  
  public static final class Synchronized extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.SynchronizedStatement value;
    
    public Synchronized (hydra.langs.java.syntax.SynchronizedStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Synchronized)) {
        return false;
      }
      Synchronized o = (Synchronized) (other);
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
  
  public static final class Throw extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.ThrowStatement value;
    
    public Throw (hydra.langs.java.syntax.ThrowStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Throw)) {
        return false;
      }
      Throw o = (Throw) (other);
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
  
  public static final class Try extends hydra.langs.java.syntax.StatementWithoutTrailingSubstatement implements Serializable {
    public final hydra.langs.java.syntax.TryStatement value;
    
    public Try (hydra.langs.java.syntax.TryStatement value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Try)) {
        return false;
      }
      Try o = (Try) (other);
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
}