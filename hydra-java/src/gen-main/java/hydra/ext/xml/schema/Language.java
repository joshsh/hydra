package hydra.ext.xml.schema;

public class Language {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/ext/xml/schema.Language");
  
  public final String value;
  
  public Language (String value) {
    this.value = value;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Language)) {
      return false;
    }
    Language o = (Language) (other);
    return value.equals(o.value);
  }
  
  @Override
  public int hashCode() {
    return 2 * value.hashCode();
  }
}