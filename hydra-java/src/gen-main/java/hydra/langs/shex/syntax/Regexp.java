// Note: this is an automatically generated file. Do not edit.

package hydra.langs.shex.syntax;

import java.io.Serializable;

public class Regexp implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Regexp");
  
  public final java.util.List<hydra.langs.shex.syntax.Regexp_ListOfAlts_Elmt> listOfAlts;
  
  public final java.util.List<String> listOfRegex;
  
  public Regexp (java.util.List<hydra.langs.shex.syntax.Regexp_ListOfAlts_Elmt> listOfAlts, java.util.List<String> listOfRegex) {
    if (listOfAlts == null) {
      throw new IllegalArgumentException("null value for 'listOfAlts' argument");
    }
    if (listOfRegex == null) {
      throw new IllegalArgumentException("null value for 'listOfRegex' argument");
    }
    this.listOfAlts = listOfAlts;
    this.listOfRegex = listOfRegex;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Regexp)) {
      return false;
    }
    Regexp o = (Regexp) (other);
    return listOfAlts.equals(o.listOfAlts) && listOfRegex.equals(o.listOfRegex);
  }
  
  @Override
  public int hashCode() {
    return 2 * listOfAlts.hashCode() + 3 * listOfRegex.hashCode();
  }
  
  public Regexp withListOfAlts(java.util.List<hydra.langs.shex.syntax.Regexp_ListOfAlts_Elmt> listOfAlts) {
    if (listOfAlts == null) {
      throw new IllegalArgumentException("null value for 'listOfAlts' argument");
    }
    return new Regexp(listOfAlts, listOfRegex);
  }
  
  public Regexp withListOfRegex(java.util.List<String> listOfRegex) {
    if (listOfRegex == null) {
      throw new IllegalArgumentException("null value for 'listOfRegex' argument");
    }
    return new Regexp(listOfAlts, listOfRegex);
  }
}