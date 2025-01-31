package hydra.pg.dsl;

import hydra.pg.model.Vertex;
import hydra.pg.model.VertexLabel;

/**
 * A builder object for property graph vertices.
 */
public class VertexBuilder<V> extends ElementBuilder<V, Vertex<V>, VertexBuilder<V>> {
    private final VertexLabel label;
    private final V id;

    /**
     * Construct the builder object.
     */
    public VertexBuilder(VertexLabel label, V id) {
        this.label = label;
        this.id = id;
    }

    @Override
    protected VertexBuilder<V> getThis() {
        return this;
    }

    @Override
    public Vertex<V> build() {
        return new Vertex<V>(label, id, properties);
    }
}
