package hydra.langs.shex.syntax;

import java.io.Serializable;

public class Uchar_Sequence2 implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shex/syntax.Uchar.Sequence2");
  
  public final hydra.langs.shex.syntax.Hex hex;
  
  public final hydra.langs.shex.syntax.Hex hex2;
  
  public final hydra.langs.shex.syntax.Hex hex3;
  
  public final hydra.langs.shex.syntax.Hex hex4;
  
  public final hydra.langs.shex.syntax.Hex hex5;
  
  public final hydra.langs.shex.syntax.Hex hex6;
  
  public final hydra.langs.shex.syntax.Hex hex7;
  
  public final hydra.langs.shex.syntax.Hex hex8;
  
  public Uchar_Sequence2 (hydra.langs.shex.syntax.Hex hex, hydra.langs.shex.syntax.Hex hex2, hydra.langs.shex.syntax.Hex hex3, hydra.langs.shex.syntax.Hex hex4, hydra.langs.shex.syntax.Hex hex5, hydra.langs.shex.syntax.Hex hex6, hydra.langs.shex.syntax.Hex hex7, hydra.langs.shex.syntax.Hex hex8) {
    this.hex = hex;
    this.hex2 = hex2;
    this.hex3 = hex3;
    this.hex4 = hex4;
    this.hex5 = hex5;
    this.hex6 = hex6;
    this.hex7 = hex7;
    this.hex8 = hex8;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Uchar_Sequence2)) {
      return false;
    }
    Uchar_Sequence2 o = (Uchar_Sequence2) (other);
    return hex.equals(o.hex) && hex2.equals(o.hex2) && hex3.equals(o.hex3) && hex4.equals(o.hex4) && hex5.equals(o.hex5) && hex6.equals(o.hex6) && hex7.equals(o.hex7) && hex8.equals(o.hex8);
  }
  
  @Override
  public int hashCode() {
    return 2 * hex.hashCode() + 3 * hex2.hashCode() + 5 * hex3.hashCode() + 7 * hex4.hashCode() + 11 * hex5.hashCode() + 13 * hex6.hashCode() + 17 * hex7.hashCode() + 19 * hex8.hashCode();
  }
  
  public Uchar_Sequence2 withHex(hydra.langs.shex.syntax.Hex hex) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
  
  public Uchar_Sequence2 withHex2(hydra.langs.shex.syntax.Hex hex2) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
  
  public Uchar_Sequence2 withHex3(hydra.langs.shex.syntax.Hex hex3) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
  
  public Uchar_Sequence2 withHex4(hydra.langs.shex.syntax.Hex hex4) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
  
  public Uchar_Sequence2 withHex5(hydra.langs.shex.syntax.Hex hex5) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
  
  public Uchar_Sequence2 withHex6(hydra.langs.shex.syntax.Hex hex6) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
  
  public Uchar_Sequence2 withHex7(hydra.langs.shex.syntax.Hex hex7) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
  
  public Uchar_Sequence2 withHex8(hydra.langs.shex.syntax.Hex hex8) {
    return new Uchar_Sequence2(hex, hex2, hex3, hex4, hex5, hex6, hex7, hex8);
  }
}