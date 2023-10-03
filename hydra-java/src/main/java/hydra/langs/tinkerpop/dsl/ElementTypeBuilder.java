package hydra.langs.tinkerpop.dsl;

import hydra.langs.tinkerpop.propertyGraph.PropertyKey;
import hydra.langs.tinkerpop.propertyGraph.PropertyType;

import java.util.ArrayList;
import java.util.List;

public abstract class ElementTypeBuilder<T, S, B extends ElementTypeBuilder<T, S, B>> {
    protected final List<PropertyType<T>> properties = new ArrayList<>();
    protected abstract B getThis();
    public abstract S build();

    public B property(String key, T type, boolean required) {
        properties.add(new PropertyType<T>(new PropertyKey(key), type, required));
        return getThis();
    }
}
