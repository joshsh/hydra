// Note: this is an automatically generated file. Do not edit.

package hydra.ast;

import hydra.util.Opt;

import java.io.Serializable;

/**
 * Formatting option for code blocks
 */
public class BlockStyle implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ast.BlockStyle");
  
  public final Opt<String> indent;
  
  public final Boolean newlineBeforeContent;
  
  public final Boolean newlineAfterContent;
  
  public BlockStyle (Opt<String> indent, Boolean newlineBeforeContent, Boolean newlineAfterContent) {
    if (indent == null) {
      throw new IllegalArgumentException("null value for 'indent' argument");
    }
    if (newlineBeforeContent == null) {
      throw new IllegalArgumentException("null value for 'newlineBeforeContent' argument");
    }
    if (newlineAfterContent == null) {
      throw new IllegalArgumentException("null value for 'newlineAfterContent' argument");
    }
    this.indent = indent;
    this.newlineBeforeContent = newlineBeforeContent;
    this.newlineAfterContent = newlineAfterContent;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof BlockStyle)) {
      return false;
    }
    BlockStyle o = (BlockStyle) (other);
    return indent.equals(o.indent) && newlineBeforeContent.equals(o.newlineBeforeContent) && newlineAfterContent.equals(o.newlineAfterContent);
  }
  
  @Override
  public int hashCode() {
    return 2 * indent.hashCode() + 3 * newlineBeforeContent.hashCode() + 5 * newlineAfterContent.hashCode();
  }
  
  public BlockStyle withIndent(Opt<String> indent) {
    if (indent == null) {
      throw new IllegalArgumentException("null value for 'indent' argument");
    }
    return new BlockStyle(indent, newlineBeforeContent, newlineAfterContent);
  }
  
  public BlockStyle withNewlineBeforeContent(Boolean newlineBeforeContent) {
    if (newlineBeforeContent == null) {
      throw new IllegalArgumentException("null value for 'newlineBeforeContent' argument");
    }
    return new BlockStyle(indent, newlineBeforeContent, newlineAfterContent);
  }
  
  public BlockStyle withNewlineAfterContent(Boolean newlineAfterContent) {
    if (newlineAfterContent == null) {
      throw new IllegalArgumentException("null value for 'newlineAfterContent' argument");
    }
    return new BlockStyle(indent, newlineBeforeContent, newlineAfterContent);
  }
}
