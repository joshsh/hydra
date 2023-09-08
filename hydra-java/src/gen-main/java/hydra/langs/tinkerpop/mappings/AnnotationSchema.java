package hydra.langs.tinkerpop.mappings;

import java.io.Serializable;

/**
 * Configurable annotation keys for property graph mapping specifications
 */
public class AnnotationSchema implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/mappings.AnnotationSchema");
  
  public final String vertexLabel;
  
  public final String edgeLabel;
  
  public final String vertexId;
  
  public final String edgeId;
  
  public final String propertyKey;
  
  public final String propertyValue;
  
  public final String outVertex;
  
  public final String outVertexLabel;
  
  public final String inVertex;
  
  public final String inVertexLabel;
  
  public final String outEdge;
  
  public final String outEdgeLabel;
  
  public final String inEdge;
  
  public final String inEdgeLabel;
  
  public final String ignore;
  
  public AnnotationSchema (String vertexLabel, String edgeLabel, String vertexId, String edgeId, String propertyKey, String propertyValue, String outVertex, String outVertexLabel, String inVertex, String inVertexLabel, String outEdge, String outEdgeLabel, String inEdge, String inEdgeLabel, String ignore) {
    this.vertexLabel = vertexLabel;
    this.edgeLabel = edgeLabel;
    this.vertexId = vertexId;
    this.edgeId = edgeId;
    this.propertyKey = propertyKey;
    this.propertyValue = propertyValue;
    this.outVertex = outVertex;
    this.outVertexLabel = outVertexLabel;
    this.inVertex = inVertex;
    this.inVertexLabel = inVertexLabel;
    this.outEdge = outEdge;
    this.outEdgeLabel = outEdgeLabel;
    this.inEdge = inEdge;
    this.inEdgeLabel = inEdgeLabel;
    this.ignore = ignore;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof AnnotationSchema)) {
      return false;
    }
    AnnotationSchema o = (AnnotationSchema) (other);
    return vertexLabel.equals(o.vertexLabel) && edgeLabel.equals(o.edgeLabel) && vertexId.equals(o.vertexId) && edgeId.equals(o.edgeId) && propertyKey.equals(o.propertyKey) && propertyValue.equals(o.propertyValue) && outVertex.equals(o.outVertex) && outVertexLabel.equals(o.outVertexLabel) && inVertex.equals(o.inVertex) && inVertexLabel.equals(o.inVertexLabel) && outEdge.equals(o.outEdge) && outEdgeLabel.equals(o.outEdgeLabel) && inEdge.equals(o.inEdge) && inEdgeLabel.equals(o.inEdgeLabel) && ignore.equals(o.ignore);
  }
  
  @Override
  public int hashCode() {
    return 2 * vertexLabel.hashCode() + 3 * edgeLabel.hashCode() + 5 * vertexId.hashCode() + 7 * edgeId.hashCode() + 11 * propertyKey.hashCode() + 13 * propertyValue.hashCode() + 17 * outVertex.hashCode() + 19 * outVertexLabel.hashCode() + 23 * inVertex.hashCode() + 29 * inVertexLabel.hashCode() + 31 * outEdge.hashCode() + 37 * outEdgeLabel.hashCode() + 41 * inEdge.hashCode() + 43 * inEdgeLabel.hashCode() + 47 * ignore.hashCode();
  }
  
  public AnnotationSchema withVertexLabel(String vertexLabel) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withEdgeLabel(String edgeLabel) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withVertexId(String vertexId) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withEdgeId(String edgeId) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withPropertyKey(String propertyKey) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withPropertyValue(String propertyValue) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withOutVertex(String outVertex) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withOutVertexLabel(String outVertexLabel) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withInVertex(String inVertex) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withInVertexLabel(String inVertexLabel) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withOutEdge(String outEdge) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withOutEdgeLabel(String outEdgeLabel) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withInEdge(String inEdge) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withInEdgeLabel(String inEdgeLabel) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
  
  public AnnotationSchema withIgnore(String ignore) {
    return new AnnotationSchema(vertexLabel, edgeLabel, vertexId, edgeId, propertyKey, propertyValue, outVertex, outVertexLabel, inVertex, inVertexLabel, outEdge, outEdgeLabel, inEdge, inEdgeLabel, ignore);
  }
}