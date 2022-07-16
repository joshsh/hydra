package hydra.ext.scala.meta;

public class Type_Match {
  public final Type tpe;
  
  public final java.util.List<TypeCase> cases;
  
  public Type_Match (Type tpe, java.util.List<TypeCase> cases) {
    this.tpe = tpe;
    this.cases = cases;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Type_Match)) {
      return false;
    }
    Type_Match o = (Type_Match) (other);
    return tpe.equals(o.tpe) && cases.equals(o.cases);
  }
  
  @Override
  public int hashCode() {
    return 2 * tpe.hashCode() + 3 * cases.hashCode();
  }
  
  public Type_Match withTpe(Type tpe) {
    return new Type_Match(tpe, cases);
  }
  
  public Type_Match withCases(java.util.List<TypeCase> cases) {
    return new Type_Match(tpe, cases);
  }
}