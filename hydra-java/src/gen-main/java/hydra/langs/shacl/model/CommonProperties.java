package hydra.langs.shacl.model;

import java.io.Serializable;

/**
 * Common constraint parameters and other properties for SHACL shapes
 */
public class CommonProperties implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/shacl/model.CommonProperties");
  
  /**
   * Common constraint parameters attached to this shape
   */
  public final java.util.Set<hydra.langs.shacl.model.CommonConstraint> constraints;
  
  /**
   * See https://www.w3.org/TR/shacl/#deactivated
   */
  public final java.util.Optional<Boolean> deactivated;
  
  /**
   * See https://www.w3.org/TR/shacl/#message
   */
  public final hydra.langs.rdf.syntax.LangStrings message;
  
  /**
   * See https://www.w3.org/TR/shacl/#severity
   */
  public final hydra.langs.shacl.model.Severity severity;
  
  /**
   * See https://www.w3.org/TR/shacl/#targetClass
   */
  public final java.util.Set<hydra.langs.rdf.syntax.RdfsClass> targetClass;
  
  /**
   * See https://www.w3.org/TR/shacl/#targetNode
   */
  public final java.util.Set<hydra.langs.rdf.syntax.IriOrLiteral> targetNode;
  
  /**
   * See https://www.w3.org/TR/shacl/#targetObjectsOf
   */
  public final java.util.Set<hydra.langs.rdf.syntax.Property> targetObjectsOf;
  
  /**
   * See https://www.w3.org/TR/shacl/#targetSubjectsOf
   */
  public final java.util.Set<hydra.langs.rdf.syntax.Property> targetSubjectsOf;
  
  public CommonProperties (java.util.Set<hydra.langs.shacl.model.CommonConstraint> constraints, java.util.Optional<Boolean> deactivated, hydra.langs.rdf.syntax.LangStrings message, hydra.langs.shacl.model.Severity severity, java.util.Set<hydra.langs.rdf.syntax.RdfsClass> targetClass, java.util.Set<hydra.langs.rdf.syntax.IriOrLiteral> targetNode, java.util.Set<hydra.langs.rdf.syntax.Property> targetObjectsOf, java.util.Set<hydra.langs.rdf.syntax.Property> targetSubjectsOf) {
    this.constraints = constraints;
    this.deactivated = deactivated;
    this.message = message;
    this.severity = severity;
    this.targetClass = targetClass;
    this.targetNode = targetNode;
    this.targetObjectsOf = targetObjectsOf;
    this.targetSubjectsOf = targetSubjectsOf;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof CommonProperties)) {
      return false;
    }
    CommonProperties o = (CommonProperties) (other);
    return constraints.equals(o.constraints) && deactivated.equals(o.deactivated) && message.equals(o.message) && severity.equals(o.severity) && targetClass.equals(o.targetClass) && targetNode.equals(o.targetNode) && targetObjectsOf.equals(o.targetObjectsOf) && targetSubjectsOf.equals(o.targetSubjectsOf);
  }
  
  @Override
  public int hashCode() {
    return 2 * constraints.hashCode() + 3 * deactivated.hashCode() + 5 * message.hashCode() + 7 * severity.hashCode() + 11 * targetClass.hashCode() + 13 * targetNode.hashCode() + 17 * targetObjectsOf.hashCode() + 19 * targetSubjectsOf.hashCode();
  }
  
  public CommonProperties withConstraints(java.util.Set<hydra.langs.shacl.model.CommonConstraint> constraints) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
  
  public CommonProperties withDeactivated(java.util.Optional<Boolean> deactivated) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
  
  public CommonProperties withMessage(hydra.langs.rdf.syntax.LangStrings message) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
  
  public CommonProperties withSeverity(hydra.langs.shacl.model.Severity severity) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
  
  public CommonProperties withTargetClass(java.util.Set<hydra.langs.rdf.syntax.RdfsClass> targetClass) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
  
  public CommonProperties withTargetNode(java.util.Set<hydra.langs.rdf.syntax.IriOrLiteral> targetNode) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
  
  public CommonProperties withTargetObjectsOf(java.util.Set<hydra.langs.rdf.syntax.Property> targetObjectsOf) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
  
  public CommonProperties withTargetSubjectsOf(java.util.Set<hydra.langs.rdf.syntax.Property> targetSubjectsOf) {
    return new CommonProperties(constraints, deactivated, message, severity, targetClass, targetNode, targetObjectsOf, targetSubjectsOf);
  }
}