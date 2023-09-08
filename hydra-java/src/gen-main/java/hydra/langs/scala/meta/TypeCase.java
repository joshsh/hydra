package hydra.langs.scala.meta;

import java.io.Serializable;

public class TypeCase implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.TypeCase");
  
  public final hydra.langs.scala.meta.Type pat;
  
  public final hydra.langs.scala.meta.Type body;
  
  public TypeCase (hydra.langs.scala.meta.Type pat, hydra.langs.scala.meta.Type body) {
    this.pat = pat;
    this.body = body;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof TypeCase)) {
      return false;
    }
    TypeCase o = (TypeCase) (other);
    return pat.equals(o.pat) && body.equals(o.body);
  }
  
  @Override
  public int hashCode() {
    return 2 * pat.hashCode() + 3 * body.hashCode();
  }
  
  public TypeCase withPat(hydra.langs.scala.meta.Type pat) {
    return new TypeCase(pat, body);
  }
  
  public TypeCase withBody(hydra.langs.scala.meta.Type body) {
    return new TypeCase(pat, body);
  }
}