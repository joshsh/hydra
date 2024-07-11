// Note: this is an automatically generated file. Do not edit.

package hydra.langs.scala.meta;

import java.io.Serializable;

public class Defn_Trait implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/scala/meta.Defn.Trait");
  
  public final java.util.List<hydra.langs.scala.meta.Mod> mods;
  
  public final hydra.langs.scala.meta.Type_Name name;
  
  public final java.util.List<hydra.langs.scala.meta.Type_Param> tparams;
  
  public final hydra.langs.scala.meta.Ctor_Primary ctor;
  
  public final hydra.langs.scala.meta.Template template;
  
  public Defn_Trait (java.util.List<hydra.langs.scala.meta.Mod> mods, hydra.langs.scala.meta.Type_Name name, java.util.List<hydra.langs.scala.meta.Type_Param> tparams, hydra.langs.scala.meta.Ctor_Primary ctor, hydra.langs.scala.meta.Template template) {
    java.util.Objects.requireNonNull((mods));
    java.util.Objects.requireNonNull((name));
    java.util.Objects.requireNonNull((tparams));
    java.util.Objects.requireNonNull((ctor));
    java.util.Objects.requireNonNull((template));
    this.mods = mods;
    this.name = name;
    this.tparams = tparams;
    this.ctor = ctor;
    this.template = template;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof Defn_Trait)) {
      return false;
    }
    Defn_Trait o = (Defn_Trait) (other);
    return mods.equals(o.mods) && name.equals(o.name) && tparams.equals(o.tparams) && ctor.equals(o.ctor) && template.equals(o.template);
  }
  
  @Override
  public int hashCode() {
    return 2 * mods.hashCode() + 3 * name.hashCode() + 5 * tparams.hashCode() + 7 * ctor.hashCode() + 11 * template.hashCode();
  }
  
  public Defn_Trait withMods(java.util.List<hydra.langs.scala.meta.Mod> mods) {
    java.util.Objects.requireNonNull((mods));
    return new Defn_Trait(mods, name, tparams, ctor, template);
  }
  
  public Defn_Trait withName(hydra.langs.scala.meta.Type_Name name) {
    java.util.Objects.requireNonNull((name));
    return new Defn_Trait(mods, name, tparams, ctor, template);
  }
  
  public Defn_Trait withTparams(java.util.List<hydra.langs.scala.meta.Type_Param> tparams) {
    java.util.Objects.requireNonNull((tparams));
    return new Defn_Trait(mods, name, tparams, ctor, template);
  }
  
  public Defn_Trait withCtor(hydra.langs.scala.meta.Ctor_Primary ctor) {
    java.util.Objects.requireNonNull((ctor));
    return new Defn_Trait(mods, name, tparams, ctor, template);
  }
  
  public Defn_Trait withTemplate(hydra.langs.scala.meta.Template template) {
    java.util.Objects.requireNonNull((template));
    return new Defn_Trait(mods, name, tparams, ctor, template);
  }
}