package hydra.graph;

import java.io.Serializable;

/**
 * A graph element, having a name, data term (value), and schema term (type)
 */
public class Element<A> implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/graph.Element");
  
  public final hydra.core.Name name;
  
  public final hydra.core.Term<A> data;
  
  public Element (hydra.core.Name name, hydra.core.Term<A> data) {
    this.name = name;
    this.data = data;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Element)) {
      return false;
    }
    Element o = (Element) (other);
    return name.equals(o.name) && data.equals(o.data);
  }
  
  @Override
  public int hashCode() {
    return 2 * name.hashCode() + 3 * data.hashCode();
  }
  
  public Element withName(hydra.core.Name name) {
    return new Element(name, data);
  }
  
  public Element withData(hydra.core.Term<A> data) {
    return new Element(name, data);
  }
}