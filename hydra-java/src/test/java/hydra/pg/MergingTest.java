package hydra.pg;

import hydra.dsl.Flows;
import hydra.compute.Flow;
import hydra.compute.StatelessAdapter;
import hydra.core.Literal;
import hydra.core.LiteralType;
import hydra.core.Unit;
import hydra.dsl.LiteralTypes;
import hydra.dsl.Literals;
import hydra.pg.model.Edge;
import hydra.pg.model.EdgeType;
import hydra.pg.model.PropertyKey;
import hydra.pg.model.Vertex;
import hydra.pg.model.VertexType;
import java.util.Arrays;
import java.util.List;
import org.junit.jupiter.api.Test;


public class MergingTest extends PropertyGraphTestBase {
    private static final boolean DO_NOT_UNIFY = false;
    private static final boolean UNIFY = true;

    @Test
    public void testFailOnEmptyListOfInputTypes() {
        assertFails(Merging.createVertexAdapter(Arrays.asList(), Merging.STRING_ID_ADAPTERS, DO_NOT_UNIFY));
        assertFails(Merging.createEdgeAdapter(Arrays.asList(), Merging.STRING_ID_ADAPTERS, DO_NOT_UNIFY));
    }

    @Test
    public void failOnDuplicateLabels() {
        assertFails(Merging.createVertexAdapter(
                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_PERSON_C),
                Merging.STRING_ID_ADAPTERS, DO_NOT_UNIFY));
        assertFails(Merging.createEdgeAdapter(
                Arrays.asList(EDGE_TYPE_WORKSAT_A, EDGE_TYPE_WORKSAT_C),
                Merging.STRING_ID_ADAPTERS, DO_NOT_UNIFY));
    }

    @Test
    public void testVertexTypeIsAsExpectedWithoutUnification() {
        boolean unify = DO_NOT_UNIFY;
        assertSucceedsWith(2,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.source.size()));
        assertSucceedsWith(Merging.DEFAULT_VERTEX_LABEL,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.label));
        assertSucceedsWith(9,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.size()));
        assertSucceedsWith(false,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.isLossy));

        assertSucceedsWith("person_name",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(0).key.value));
        assertSucceedsWith("person_nickname",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(1).key.value));
        assertSucceedsWith("person_age",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(2).key.value));
        assertSucceedsWith("person_birthTimeUnixMilliseconds",
            Flows.map(Merging.createVertexAdapter(
                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                Merging.STRING_ID_ADAPTERS,
                unify),
                adapter -> adapter.target.properties.get(3).key.value));
        assertSucceedsWith("organization_name",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(4).key.value));
        assertSucceedsWith("organization_nickname",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(5).key.value));
        assertSucceedsWith("organization_age",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(6).key.value));
        assertSucceedsWith("organization_industry",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(7).key.value));

        assertSucceedsWith(false,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(0).required));
        assertSucceedsWith(LiteralTypes.string(),
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(0).value));
    }

    @Test
    public void testVertexTypeIsAsExpectedWithUnification() {
        boolean unify = UNIFY;

        assertSucceedsWith(2,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.source.size()));
        assertSucceedsWith(Merging.DEFAULT_VERTEX_LABEL,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.label));
        assertSucceedsWith(7,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.size()));
        assertSucceedsWith(false,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.isLossy));

        assertSucceedsWith("name",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(0).key.value));
        assertSucceedsWith("nickname",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(1).key.value));
        assertSucceedsWith("person_age",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(2).key.value));
        assertSucceedsWith("birthTimeUnixMilliseconds",
            Flows.map(Merging.createVertexAdapter(
                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                Merging.STRING_ID_ADAPTERS,
                unify),
                adapter -> adapter.target.properties.get(3).key.value));
        assertSucceedsWith("organization_age",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(4).key.value));
        assertSucceedsWith("industry",
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(5).key.value));

        // The "name" property is required, because it is required in all component vertex types
        assertSucceedsWith(true,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(0).required));
        assertSucceedsWith(LiteralTypes.string(),
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(0).value));
        // The "nickname" property is not required, because it is not required in Person
        // (even though it is required in Organization).
        assertSucceedsWith(false,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(1).required));
        // The "person_age" and "organization_age" properties are not required, because they differ in datatype
        assertSucceedsWith(false,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(2).required));
        assertSucceedsWith(LiteralTypes.int32(),
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(2).value));
        assertSucceedsWith(false,
            Flows.map(Merging.createVertexAdapter(
                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                Merging.STRING_ID_ADAPTERS,
                unify),
                adapter -> adapter.target.properties.get(3).required));
        assertSucceedsWith(LiteralTypes.uint64(),
            Flows.map(Merging.createVertexAdapter(
                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                Merging.STRING_ID_ADAPTERS,
                unify),
                adapter -> adapter.target.properties.get(3).value));
        assertSucceedsWith(false,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(4).required));
        assertSucceedsWith(LiteralTypes.int64(),
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(4).value));
        // The "industry" property, while required in Organization, is not required in the merged type
        // because it is not present in Person.
        assertSucceedsWith(false,
                Flows.map(Merging.createVertexAdapter(
                                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                                Merging.STRING_ID_ADAPTERS,
                                unify),
                        adapter -> adapter.target.properties.get(5).required));
    }

    @Test
    public void testVertexEncodingIsAsExpectedWithoutUnification() {
        boolean unify = DO_NOT_UNIFY;

        assertSucceedsWith(Literals.string("person_arthur"), Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.id));
        assertSucceedsWith(VERTEX_PERSON_1.label, Flows.map(encodeVertex(VERTEX_PERSON_1, unify), v -> v.label));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("name")) == null));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("organization_name")) == null));
        assertSucceedsWith(Literals.string("Arthur Dent"), Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("person_name"))));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("person_nickname")) == null));
        assertSucceedsWith(Literals.int32(42), Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("person_age"))));

        assertSucceedsWith(Literals.string("Ford Prefect"), Flows.map(encodeVertex(VERTEX_PERSON_2, unify),
                v -> v.properties.get(new PropertyKey("person_name"))));
        assertSucceedsWith(Literals.string("Ix"), Flows.map(encodeVertex(VERTEX_PERSON_2, unify),
                v -> v.properties.get(new PropertyKey("person_nickname"))));

        assertSucceedsWith(Literals.string("organization_megadodo"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify), v -> v.id));
        assertSucceedsWith(VERTEX_ORGANIZATION_1.label,
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify), v -> v.label));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                v -> v.properties.get(new PropertyKey("name")) == null));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                v -> v.properties.get(new PropertyKey("person_name")) == null));
        assertSucceedsWith(Literals.string("Megadodo Publications"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                        v -> v.properties.get(new PropertyKey("organization_name"))));
        assertSucceedsWith(Literals.string("publishers"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                        v -> v.properties.get(new PropertyKey("organization_industry"))));
        assertSucceedsWith(Literals.int32(1000042),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                        v -> v.properties.get(new PropertyKey("organization_numberOfEmployees"))));

        assertSucceedsWith(Literals.string("Infinidim Enterprises"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_2, unify),
                        v -> v.properties.get(new PropertyKey("organization_name"))));
        assertSucceedsWith(Literals.string("all-powerful conglomerates"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_2, unify),
                        v -> v.properties.get(new PropertyKey("organization_industry"))));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_ORGANIZATION_2, unify),
                v -> v.properties.get(new PropertyKey("organization_numberOfEmployees")) == null));
    }

    @Test
    public void testVertexEncodingIsAsExpectedWithUnification() {
        boolean unify = UNIFY;

        assertSucceedsWith(Literals.string("person_arthur"), Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.id));
        assertSucceedsWith(VERTEX_PERSON_1.label, Flows.map(encodeVertex(VERTEX_PERSON_1, unify), v -> v.label));
        assertSucceedsWith(Literals.string("Arthur Dent"), Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("name"))));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("nickname")) == null));
        assertSucceedsWith(Literals.int32(42), Flows.map(encodeVertex(VERTEX_PERSON_1, unify),
                v -> v.properties.get(new PropertyKey("person_age"))));

        assertSucceedsWith(Literals.string("Ford Prefect"), Flows.map(encodeVertex(VERTEX_PERSON_2, unify),
                v -> v.properties.get(new PropertyKey("name"))));
        assertSucceedsWith(Literals.string("Ix"), Flows.map(encodeVertex(VERTEX_PERSON_2, unify),
                v -> v.properties.get(new PropertyKey("nickname"))));

        assertSucceedsWith(Literals.string("organization_megadodo"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                        v -> v.id));
        assertSucceedsWith(VERTEX_ORGANIZATION_1.label,
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify), v -> v.label));
        assertSucceedsWith(Literals.string("Megadodo Publications"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                        v -> v.properties.get(new PropertyKey("name"))));
        assertSucceedsWith(Literals.string("Megadodo"), Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                v -> v.properties.get(new PropertyKey("nickname"))));
        assertSucceedsWith(Literals.string("publishers"), Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                v -> v.properties.get(new PropertyKey("industry"))));
        assertSucceedsWith(Literals.int32(1000042), Flows.map(encodeVertex(VERTEX_ORGANIZATION_1, unify),
                v -> v.properties.get(new PropertyKey("numberOfEmployees"))));

        assertSucceedsWith(Literals.string("Infinidim Enterprises"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_2, unify),
                        v -> v.properties.get(new PropertyKey("name"))));
        assertSucceedsWith(Literals.string("Infinidim"), Flows.map(encodeVertex(VERTEX_ORGANIZATION_2, unify),
                v -> v.properties.get(new PropertyKey("nickname"))));
        assertSucceedsWith(Literals.string("all-powerful conglomerates"),
                Flows.map(encodeVertex(VERTEX_ORGANIZATION_2, unify),
                        v -> v.properties.get(new PropertyKey("industry"))));
        assertSucceedsWith(true, Flows.map(encodeVertex(VERTEX_ORGANIZATION_2, unify),
                v -> v.properties.get(new PropertyKey("numberOfEmployees")) == null));
    }

    // Note: merged edge types, and property unification are not specifically tested here,
    // as nearly all of the logic is common to vertices and edges.
    @Test
    public void testEdgeEncodingIsAsExpected() {
        boolean unify = DO_NOT_UNIFY;

        assertSucceedsWith(Literals.string("worksAt_ford-megadodo"), Flows.map(encodeEdge(EDGE_WORKSAT_1, unify),
                e -> e.id));
        assertSucceedsWith(EDGE_WORKSAT_1.label, Flows.map(encodeEdge(EDGE_WORKSAT_1, unify),
                e -> e.label));
        assertSucceedsWith(Literals.string("person_ford"), Flows.map(encodeEdge(EDGE_WORKSAT_1, unify),
                e -> e.out));
        assertSucceedsWith(Literals.string("organization_megadodo"), Flows.map(encodeEdge(EDGE_WORKSAT_1, unify),
                e -> e.in));
        assertSucceedsWith(true, Flows.map(encodeEdge(EDGE_WORKSAT_1, unify),
                v -> v.properties.get(new PropertyKey("employeeStatus")) == null));
        assertSucceedsWith(Literals.string("current"), Flows.map(encodeEdge(EDGE_WORKSAT_1, unify),
                v -> v.properties.get(new PropertyKey("worksAt_employeeStatus"))));

        assertSucceedsWith(Literals.string("person_hoopy"), Flows.map(encodeEdge(EDGE_FOUNDED_1, unify),
                e -> e.out));
        assertSucceedsWith(Literals.string("organization_megadodo"), Flows.map(encodeEdge(EDGE_FOUNDED_1, unify),
                e -> e.in));
        assertSucceedsWith(Literals.float32(51.0f), Flows.map(encodeEdge(EDGE_FOUNDED_1, unify),
                v -> v.properties.get(new PropertyKey("founded_ownershipPercentage"))));

        assertSucceedsWith(Literals.string("organization_megadodo"), Flows.map(encodeEdge(EDGE_PARTOF_1, unify),
                e -> e.out));
        assertSucceedsWith(Literals.string("organization_infinidim"), Flows.map(encodeEdge(EDGE_PARTOF_1, unify),
                e -> e.in));
    }

    @Test
    public void testVertexRoundTripsAreNoop() {
        Flow<Unit, StatelessAdapter<
                List<VertexType<LiteralType>>,
                VertexType<LiteralType>,
                Vertex<Literal>,
                Vertex<Literal>>> adapterFlow
                = Merging.createVertexAdapter(
                Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                Merging.STRING_ID_ADAPTERS,
                DO_NOT_UNIFY);
        Flows.map(adapterFlow, adapter -> {
            assertRoundTripIsNoop(adapter.coder, VERTEX_PERSON_1);
            assertRoundTripIsNoop(adapter.coder, VERTEX_PERSON_2);
            assertRoundTripIsNoop(adapter.coder, VERTEX_PERSON_3);
            assertRoundTripIsNoop(adapter.coder, VERTEX_ORGANIZATION_1);
            assertRoundTripIsNoop(adapter.coder, VERTEX_ORGANIZATION_2);
            return true;
        });
    }

    @Test
    public void testEdgeRoundTripsAreNoop() {
        Flow<Unit, StatelessAdapter<
                List<EdgeType<LiteralType>>,
                EdgeType<LiteralType>,
                Edge<Literal>,
                Edge<Literal>>> adapterFlow
                = Merging.createEdgeAdapter(
                Arrays.asList(EDGE_TYPE_WORKSAT_A, EDGE_TYPE_FOUNDED, EDGE_TYPE_PARTOF),
                Merging.STRING_ID_ADAPTERS,
                DO_NOT_UNIFY);
        Flows.map(adapterFlow, adapter -> {
            assertRoundTripIsNoop(adapter.coder, EDGE_WORKSAT_1);
            assertRoundTripIsNoop(adapter.coder, EDGE_FOUNDED_1);
            assertRoundTripIsNoop(adapter.coder, EDGE_PARTOF_1);
            return true;
        });
    }

    private static Flow<Unit, Vertex<Literal>> encodeVertex(Vertex<Literal> v,
                                                            boolean unifyIdenticalTypes) {
        return Flows.bind(
                Merging.createVertexAdapter(
                        Arrays.asList(VERTEX_TYPE_PERSON_A, VERTEX_TYPE_ORGANIZATION),
                        Merging.STRING_ID_ADAPTERS,
                        unifyIdenticalTypes),
                        adapter -> adapter.coder.encode.apply(v));
    }

    private static Flow<Unit, Edge<Literal>> encodeEdge(Edge<Literal> e,
                                                        boolean unifyIdenticalTypes) {
        return Flows.bind(
                Merging.createEdgeAdapter(
                        Arrays.asList(EDGE_TYPE_WORKSAT_A, EDGE_TYPE_FOUNDED, EDGE_TYPE_PARTOF),
                        Merging.STRING_ID_ADAPTERS,
                        unifyIdenticalTypes),
                        adapter -> adapter.coder.encode.apply(e));
    }
}
