package hydra.ext.scala.meta;

public class Data_Placeholder {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/scala/meta.Data.Placeholder");
  
  public Data_Placeholder () {
  
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Data_Placeholder)) {
      return false;
    }
    Data_Placeholder o = (Data_Placeholder) (other);
    return true;
  }
  
  @Override
  public int hashCode() {
    return 0;
  }
}