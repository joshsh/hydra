package hydra.dsl;

import hydra.core.Name;
import hydra.core.Name;


public interface Core {
  static Name name(final String name) {
    return new Name(name);
  }
}
