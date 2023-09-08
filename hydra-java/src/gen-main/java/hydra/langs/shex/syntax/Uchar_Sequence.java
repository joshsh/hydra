package hydra.langs.shex.syntax;

import java.io.Serializable;

public class Uchar_Sequence implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Uchar.Sequence");
  
  public final hydra.langs.shex.syntax.Hex hex;
  
  public final hydra.langs.shex.syntax.Hex hex2;
  
  public final hydra.langs.shex.syntax.Hex hex3;
  
  public final hydra.langs.shex.syntax.Hex hex4;
  
  public Uchar_Sequence (hydra.langs.shex.syntax.Hex hex, hydra.langs.shex.syntax.Hex hex2, hydra.langs.shex.syntax.Hex hex3, hydra.langs.shex.syntax.Hex hex4) {
    this.hex = hex;
    this.hex2 = hex2;
    this.hex3 = hex3;
    this.hex4 = hex4;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Uchar_Sequence)) {
      return false;
    }
    Uchar_Sequence o = (Uchar_Sequence) (other);
    return hex.equals(o.hex) && hex2.equals(o.hex2) && hex3.equals(o.hex3) && hex4.equals(o.hex4);
  }
  
  @Override
  public int hashCode() {
    return 2 * hex.hashCode() + 3 * hex2.hashCode() + 5 * hex3.hashCode() + 7 * hex4.hashCode();
  }
  
  public Uchar_Sequence withHex(hydra.langs.shex.syntax.Hex hex) {
    return new Uchar_Sequence(hex, hex2, hex3, hex4);
  }
  
  public Uchar_Sequence withHex2(hydra.langs.shex.syntax.Hex hex2) {
    return new Uchar_Sequence(hex, hex2, hex3, hex4);
  }
  
  public Uchar_Sequence withHex3(hydra.langs.shex.syntax.Hex hex3) {
    return new Uchar_Sequence(hex, hex2, hex3, hex4);
  }
  
  public Uchar_Sequence withHex4(hydra.langs.shex.syntax.Hex hex4) {
    return new Uchar_Sequence(hex, hex2, hex3, hex4);
  }
}