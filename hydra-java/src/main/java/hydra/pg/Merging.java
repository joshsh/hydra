package hydra.pg;

import hydra.dsl.Flows;
import hydra.basics.Basics;
import hydra.compute.Flow;
import hydra.compute.StatelessAdapter;
import hydra.compute.StatelessCoder;
import hydra.core.Literal;
import hydra.core.LiteralType;
import hydra.core.Unit;
import hydra.dsl.LiteralTypes;
import hydra.dsl.Literals;
import hydra.pg.model.Edge;
import hydra.pg.model.EdgeLabel;
import hydra.pg.model.EdgeType;
import hydra.pg.model.PropertyKey;
import hydra.pg.model.PropertyType;
import hydra.pg.model.Vertex;
import hydra.pg.model.VertexLabel;
import hydra.pg.model.VertexType;
import hydra.util.Opt;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;


/**
 * Utilities for combining multiple vertex or edge types into a single "merged" vertex or edge type,
 * and correspondingly encoding and decoding vertices and edges of these types.
 */
public class Merging {
    public static VertexLabel DEFAULT_VERTEX_LABEL = new VertexLabel("_Merged");
    public static EdgeLabel DEFAULT_EDGE_LABEL = new EdgeLabel("_merged");

    public static final Merging.IdAdapters<LiteralType, Literal> STRING_ID_ADAPTERS
        = stringIdAdapters(
        LiteralTypes.string(),
        new Function<Literal, Flow<Unit, String>>() {
            @Override
            public Flow<Unit, String> apply(Literal literal) {
                return literal.accept(new Literal.PartialVisitor<>() {
                    @Override
                    public Flow<Unit, String> otherwise(Literal instance) {
                        return Flows.unexpected("string literal", instance);
                    }

                    @Override
                    public Flow<Unit, String> visit(Literal.String_ instance) {
                        return Flows.pure(instance.value);
                    }
                });
            }
        },
        Literals::string);

    /**
     * Create a vertex adapter based on a list of vertex types and given id adapters.
     */
    public static <T, V> Flow<Unit, StatelessAdapter<List<VertexType<T>>, VertexType<T>, Vertex<V>, Vertex<V>>>
    createVertexAdapter(List<VertexType<T>> types,
        IdAdapters<T, V> idAdapters,
        boolean unifyIdenticalTypes) {
        return Flows.map(Flows.check(types,
            Merging::checkNontrivial,
            Merging::checkNoDuplicatedVertexLabels), safeTypes -> {
            MergedEntity<VertexType<T>> mergedType = mergeVertexTypes(safeTypes, idAdapters, unifyIdenticalTypes);
            return new StatelessAdapter<List<VertexType<T>>, VertexType<T>, Vertex<V>, Vertex<V>>(
                false, types, mergedType.entity,
                constructMergedVertexCoder(safeTypes, idAdapters, mergedType.unifiedProperties));
        });
    }

    /**
     * Create an edge adapter based on a list of edge types and given id adapters.
     */
    public static <T, V> Flow<Unit, StatelessAdapter<List<EdgeType<T>>, EdgeType<T>, Edge<V>, Edge<V>>>
    createEdgeAdapter(List<EdgeType<T>> types,
        IdAdapters<T, V> idAdapters,
        boolean unifyIdenticalTypes) {
        return Flows.map(Flows.check(types,
            Merging::checkNontrivial,
            Merging::checkNoDuplicatedEdgeLabels), safeTypes -> {
            MergedEntity<EdgeType<T>> mergedType = mergeEdgeTypes(safeTypes, idAdapters, unifyIdenticalTypes);
            return new StatelessAdapter<List<EdgeType<T>>, EdgeType<T>, Edge<V>, Edge<V>>(
                false, types, mergedType.entity,
                constructMergedEdgeCoder(safeTypes, idAdapters, mergedType.unifiedProperties));
        });
    }

    private static <A> Opt<String> checkNontrivial(List<A> types) {
        return types.isEmpty()
            ? Opt.of("No types provided")
            : Opt.empty();
    }

    private static <T> Opt<String> checkNoDuplicatedVertexLabels(List<VertexType<T>> types) {
        Set<VertexLabel> labels = new HashSet<>();
        for (VertexType<T> type : types) {
            if (!labels.add(type.label)) {
                return Opt.of("Duplicate vertex label: " + type.label);
            }
        }
        return Opt.empty();
    }

    private static <T> Opt<String> checkNoDuplicatedEdgeLabels(List<EdgeType<T>> types) {
        Set<EdgeLabel> labels = new HashSet<>();
        for (EdgeType<T> type : types) {
            if (!labels.add(type.label)) {
                return Opt.of("Duplicate edge label: " + type.label);
            }
        }
        return Opt.empty();
    }

    private static <T, V> StatelessCoder<Vertex<V>, Vertex<V>> constructMergedVertexCoder(
        List<VertexType<T>> types,
        IdAdapters<T, V> idAdapters,
        Set<PropertyKey> unifiedPropertyKeys) {
        Map<VertexLabel, StatelessCoder<Vertex<V>, Vertex<V>>> coders
            = constructVertexCoders(types, idAdapters, unifiedPropertyKeys);
        return new StatelessCoder<Vertex<V>, Vertex<V>>(
            v -> Flows.bind(getCoder(coders, v.label), coder -> coder.encode.apply(v)),
            v -> Flows.bind(getCoder(coders, v.label), coder -> coder.decode.apply(v)));
    }

    private static <T, V> StatelessCoder<Edge<V>, Edge<V>> constructMergedEdgeCoder(
        List<EdgeType<T>> types,
        IdAdapters<T, V> idAdapters,
        Set<PropertyKey> unifiedPropertyKeys) {
        Map<EdgeLabel, StatelessCoder<Edge<V>, Edge<V>>> coders
            = constructEdgeCoders(types, idAdapters, unifiedPropertyKeys);
        return new StatelessCoder<Edge<V>, Edge<V>>(
            e -> Flows.bind(getCoder(coders, e.label), coder -> coder.encode.apply(e)),
            e -> Flows.bind(getCoder(coders, e.label), coder -> coder.decode.apply(e)));
    }

    private static <T, V> StatelessCoder<Vertex<V>, Vertex<V>> constructVertexCoder(
        VertexType<T> type,
        IdAdapters<T, V> idAdapters,
        Set<PropertyKey> unifiedPropertyKeys) {
        StatelessCoder<Map<PropertyKey, V>, Map<PropertyKey, V>> propertiesCoder
            = constructPropertiesCoder(type.label.value, unifiedPropertyKeys);

        return new StatelessCoder<Vertex<V>, Vertex<V>>(
            v -> Flows.map2(
                idAdapters.forVertexId.apply(type.label).encode.apply(v.id),
                propertiesCoder.encode.apply(v.properties),
                (id, props) -> new Vertex<V>(v.label, id, props)),
            v -> Flows.map2(
                idAdapters.forVertexId.apply(type.label).decode.apply(v.id),
                propertiesCoder.decode.apply(v.properties),
                (id, props) -> new Vertex<V>(v.label, id, props)));
    }

    private static <T, V> StatelessCoder<Edge<V>, Edge<V>> constructEdgeCoder(
        EdgeType<T> type,
        IdAdapters<T, V> idAdapters,
        Set<PropertyKey> unifiedPropertyKeys) {
        StatelessCoder<Map<PropertyKey, V>, Map<PropertyKey, V>> propertiesCoder
            = constructPropertiesCoder(type.label.value, unifiedPropertyKeys);

        return new StatelessCoder<Edge<V>, Edge<V>>(
            e -> Flows.map4(
                idAdapters.forEdgeId.apply(type.label).encode.apply(e.id),
                idAdapters.forVertexId.apply(type.out).encode.apply(e.out),
                idAdapters.forVertexId.apply(type.in).encode.apply(e.in),
                propertiesCoder.encode.apply(e.properties),
                (id, outId, inId, props) -> new Edge<V>(e.label, id, outId, inId, props)),
            e -> Flows.map4(
                idAdapters.forEdgeId.apply(type.label).decode.apply(e.id),
                idAdapters.forVertexId.apply(type.out).decode.apply(e.out),
                idAdapters.forVertexId.apply(type.in).decode.apply(e.in),
                propertiesCoder.decode.apply(e.properties),
                (id, outId, inId, props) -> new Edge<V>(e.label, id, outId, inId, props)));
    }

    private static <V> StatelessCoder<Map<PropertyKey, V>, Map<PropertyKey, V>> constructPropertiesCoder(
        String label,
        Set<PropertyKey> unifiedPropertyKeys) {
        Function<Map<PropertyKey, V>, Flow<Unit, Map<PropertyKey, V>>> encode = before -> {
            Map<PropertyKey, V> after = new HashMap<PropertyKey, V>();
            for (Map.Entry<PropertyKey, V> entry : before.entrySet()) {
                after.put(encodePropertyKey(label, entry.getKey(), unifiedPropertyKeys), entry.getValue());
            }
            return Flows.pure(after);
        };

        Function<Map<PropertyKey, V>, Flow<Unit, Map<PropertyKey, V>>> decode = before -> {
            Map<PropertyKey, V> after = new HashMap<PropertyKey, V>();
            for (Map.Entry<PropertyKey, V> entry : before.entrySet()) {
                after.put(decodePropertyKey(label, entry.getKey(), unifiedPropertyKeys), entry.getValue());
            }
            return Flows.pure(after);
        };

        return new StatelessCoder<Map<PropertyKey, V>, Map<PropertyKey, V>>(encode, decode);
    }

    private static <V, T, L> Map<L, StatelessCoder<V, V>> constructCoders(
        List<T> types,
        Function<T, L> getLabel,
        Function<T, StatelessCoder<V, V>> constructCoder) {
        Map<L, StatelessCoder<V, V>> coders = new HashMap<L, StatelessCoder<V, V>>();
        for (T type : types) {
            coders.put(getLabel.apply(type), constructCoder.apply(type));
        }
        return coders;
    }

    private static <T, V> Map<VertexLabel, StatelessCoder<Vertex<V>, Vertex<V>>> constructVertexCoders(
        List<VertexType<T>> types,
        IdAdapters<T, V> idAdapters,
        Set<PropertyKey> unifiedPropertyKeys) {
        return constructCoders(types, type -> type.label,
            type -> constructVertexCoder(type, idAdapters, unifiedPropertyKeys));
    }

    private static <T, V> Map<EdgeLabel, StatelessCoder<Edge<V>, Edge<V>>> constructEdgeCoders(
        List<EdgeType<T>> types,
        IdAdapters<T, V> idAdapters,
        Set<PropertyKey> unifiedPropertyKeys) {
        return constructCoders(types, type -> type.label,
            type -> constructEdgeCoder(type, idAdapters, unifiedPropertyKeys));
    }

    private static PropertyKey encodePropertyKey(String label, PropertyKey key, Set<PropertyKey> unifiedPropertyKeys) {
        if (unifiedPropertyKeys.contains(key)) {
            return key;
        } else {
            String prefix = Basics.decapitalize(label) + "_";
            return new PropertyKey(prefix + key.value);
        }
    }

    private static PropertyKey decodePropertyKey(String label, PropertyKey key, Set<PropertyKey> unifiedPropertyKeys) {
        if (unifiedPropertyKeys.contains(key)) {
            return key;
        } else {
            return new PropertyKey(key.value.substring(label.length() + 1));
        }
    }

    private static <L, E> Flow<Unit, StatelessCoder<E, E>> getCoder(Map<L, StatelessCoder<E, E>> coders, L label) {
        StatelessCoder<E, E> helper = coders.get(label);
        return helper == null
            ? Flows.fail("No coder associated with label " + label)
            : Flows.pure(helper);
    }

    private static <T, V> MergedEntity<VertexType<T>> mergeVertexTypes(List<VertexType<T>> types,
        IdAdapters<T, V> idAdapters,
        boolean unifyIdenticalTypes) {
        MergedEntity<List<PropertyType<T>>> mergedProps = mergePropertyTypes(
            types, t -> t.label, l -> l.value, t -> t.properties, unifyIdenticalTypes);
        VertexType<T> type = new VertexType<T>(DEFAULT_VERTEX_LABEL, idAdapters.mergedVertexIdType,
            mergedProps.entity);
        return new MergedEntity<VertexType<T>>(type, mergedProps.unifiedProperties);
    }

    private static <T, V> MergedEntity<EdgeType<T>> mergeEdgeTypes(List<EdgeType<T>> types,
        IdAdapters<T, V> idAdapters,
        boolean unifyIdenticalTypes) {
        MergedEntity<List<PropertyType<T>>> mergedProps = mergePropertyTypes(
            types, t -> t.label, l -> l.value, t -> t.properties, unifyIdenticalTypes);
        EdgeType<T> type = new EdgeType<T>(DEFAULT_EDGE_LABEL, idAdapters.mergedEdgeIdType,
            DEFAULT_VERTEX_LABEL, DEFAULT_VERTEX_LABEL,
            mergedProps.entity);
        return new MergedEntity<EdgeType<T>>(type, mergedProps.unifiedProperties);
    }

    /**
     * Produces a set of merged properties together with some metadata on unification:
     * if all property types for a given key (before merging) are equal, then a single merged property type is produced
     * for that key. If any are unequal, then an individual property type is produced for each, where the key is
     * prefixed by the vertex or edge label for disambiguation.
     */
    private static <T, E, L> MergedEntity<List<PropertyType<T>>> mergePropertyTypes(
        List<E> types,
        Function<E, L> getLabel,
        Function<L, String> labelToString,
        Function<E, List<PropertyType<T>>> getProperties,
        boolean unifyIdenticalTypes) {

        // Properties to be unified across types
        Set<PropertyKey> unifiedProperties;
        // Properties which are also present in all types, and required in all types
        Set<PropertyKey> requiredProperties;

        if (unifyIdenticalTypes) {
            Map<PropertyKey, List<PropertyType<T>>> typesForPropertyKey
                = new HashMap<PropertyKey, List<PropertyType<T>>>();
            for (E type : types) {
                for (PropertyType<T> ptype : getProperties.apply(type)) {
                    List<PropertyType<T>> typesForThisKey = typesForPropertyKey
                        .computeIfAbsent(ptype.key, k -> new ArrayList<PropertyType<T>>());
                    typesForThisKey.add(ptype);
                }
            }
            unifiedProperties = new HashSet<>();
            requiredProperties = new HashSet<>();
            for (Map.Entry<PropertyKey, List<PropertyType<T>>> entry : typesForPropertyKey.entrySet()) {
                if (allPropertyTypesAreEqual(entry.getValue())) {
                    unifiedProperties.add(entry.getKey());

                    // Also make the property required if it is present and required in all types
                    if (entry.getValue().size() == types.size() && allPropertyTypesAreRequired(entry.getValue())) {
                        requiredProperties.add(entry.getKey());
                    }
                }
            }
        } else {
            unifiedProperties = Collections.emptySet();
            requiredProperties = Collections.emptySet();
        }

        List<PropertyType<T>> ptypes = new ArrayList<PropertyType<T>>();
        Set<PropertyKey> visited = new HashSet<PropertyKey>();
        for (E e : types) {
            for (PropertyType<T> ptype : getProperties.apply(e)) {
                if (unifiedProperties.contains(ptype.key)) {
                    if (visited.contains(ptype.key)) {
                        continue;
                    }
                    ptypes.add(new PropertyType<T>(ptype.key, ptype.value, requiredProperties.contains(ptype.key)));
                    visited.add(ptype.key);
                } else {
                    boolean required = ptype.required && types.size() == 1;
                    ptypes.add(new PropertyType<T>(
                        encodePropertyKey(labelToString.apply(getLabel.apply(e)), ptype.key, unifiedProperties),
                        ptype.value, required));
                }
            }
        }
        return new MergedEntity<List<PropertyType<T>>>(ptypes, unifiedProperties);
    }

    private static <T> boolean allPropertyTypesAreEqual(List<PropertyType<T>> types) {
        if (types.isEmpty()) {
            return true;
        }
        PropertyType<T> first = types.get(0);
        for (int i = 1; i < types.size(); ++i) {
            if (!types.get(i).value.equals(first.value)) {
                return false;
            }
        }
        return true;
    }

    private static <T> boolean allPropertyTypesAreRequired(List<PropertyType<T>> types) {
        for (PropertyType<T> type : types) {
            if (!type.required) {
                return false;
            }
        }
        return true;
    }

    /**
     * A helper object which defines merged vertex and edge id types, and a value coder for each vertex and edge label.
     */
    public static class IdAdapters<T, V> {
        public final T mergedVertexIdType;
        public final T mergedEdgeIdType;
        public final Function<VertexLabel, StatelessCoder<V, V>> forVertexId;
        public final Function<EdgeLabel, StatelessCoder<V, V>> forEdgeId;

        /**
         * Construct the helper object.
         */
        public IdAdapters(
            T mergedVertexIdType,
            T mergedEdgeIdType,
            Function<VertexLabel, StatelessCoder<V, V>> forVertexId,
            Function<EdgeLabel, StatelessCoder<V, V>> forEdgeId) {
            this.mergedVertexIdType = mergedVertexIdType;
            this.mergedEdgeIdType = mergedEdgeIdType;
            this.forVertexId = forVertexId;
            this.forEdgeId = forEdgeId;
        }
    }

    public static <T, V> Merging.IdAdapters<T, V> stringIdAdapters(
        T stringType,
        Function<V, Flow<Unit, String>> fromLiteral,
        Function<String, V> toLiteral) {
        return new Merging.IdAdapters<>(
            stringType,
            stringType,
            label -> StatelessCoder.of(
                literal -> Flows.map(fromLiteral.apply(literal),
                    s -> toLiteral.apply(Basics.decapitalize(label.value) + "_" + s)),
                literal -> Flows.map(fromLiteral.apply(literal),
                    id -> toLiteral.apply(id.substring(label.value.length() + 1)))),
            label -> StatelessCoder.of(
                literal -> Flows.map(fromLiteral.apply(literal),
                    s -> toLiteral.apply(Basics.decapitalize(label.value) + "_" + s)),
                literal -> Flows.map(fromLiteral.apply(literal),
                    id -> toLiteral.apply(id.substring(label.value.length() + 1)))));
    }

    private static class MergedEntity<A> {
        private final A entity;
        private final Set<PropertyKey> unifiedProperties;

        private MergedEntity(A entity, Set<PropertyKey> unifiedProperties) {
            this.entity = entity;
            this.unifiedProperties = unifiedProperties;
        }
    }
}
