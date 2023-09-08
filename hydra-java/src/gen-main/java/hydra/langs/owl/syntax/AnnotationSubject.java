package hydra.langs.owl.syntax;

import java.io.Serializable;

public abstract class AnnotationSubject implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/owl/syntax.AnnotationSubject");
  
  private AnnotationSubject () {
  
  }
  
  public abstract <R> R accept(Visitor<R> visitor) ;
  
  public interface Visitor<R> {
    R visit(Iri instance) ;
    
    R visit(AnonymousIndividual instance) ;
  }
  
  public interface PartialVisitor<R> extends Visitor<R> {
    default R otherwise(AnnotationSubject instance) {
      throw new IllegalStateException("Non-exhaustive patterns when matching: " + (instance));
    }
    
    default R visit(Iri instance) {
      return otherwise((instance));
    }
    
    default R visit(AnonymousIndividual instance) {
      return otherwise((instance));
    }
  }
  
  public static final class Iri extends hydra.langs.owl.syntax.AnnotationSubject implements Serializable {
    public final hydra.langs.rdf.syntax.Iri value;
    
    public Iri (hydra.langs.rdf.syntax.Iri value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof Iri)) {
        return false;
      }
      Iri o = (Iri) (other);
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
  
  public static final class AnonymousIndividual extends hydra.langs.owl.syntax.AnnotationSubject implements Serializable {
    public final hydra.langs.owl.syntax.AnonymousIndividual value;
    
    public AnonymousIndividual (hydra.langs.owl.syntax.AnonymousIndividual value) {
      this.value = value;
    }
    
    @Override
    public boolean equals(Object other) {
      if (!(other instanceof AnonymousIndividual)) {
        return false;
      }
      AnonymousIndividual o = (AnonymousIndividual) (other);
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