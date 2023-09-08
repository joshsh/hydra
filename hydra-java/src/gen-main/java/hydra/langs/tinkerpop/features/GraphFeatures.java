package hydra.langs.tinkerpop.features;

import java.io.Serializable;

/**
 * Features specific to a operations of a graph.
 */
public class GraphFeatures implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/tinkerpop/features.GraphFeatures");
  
  /**
   * Determines if the Graph implementation supports GraphComputer based processing.
   */
  public final Boolean supportsComputer;
  
  /**
   * Determines if the Graph implementation supports more than one connection to the same instance at the same time.
   */
  public final Boolean supportsConcurrentAccess;
  
  /**
   * Determines if the Graph implementations supports read operations as executed with the GraphTraversalSource.io(String) step.
   */
  public final Boolean supportsIoRead;
  
  /**
   * Determines if the Graph implementations supports write operations as executed with the GraphTraversalSource.io(String) step.
   */
  public final Boolean supportsIoWrite;
  
  /**
   * Determines if the Graph implementation supports persisting it's contents natively to disk.
   */
  public final Boolean supportsPersistence;
  
  /**
   * Determines if the Graph implementation supports threaded transactions which allow a transaction to be executed across multiple threads via Transaction.createThreadedTx().
   */
  public final Boolean supportsThreadedTransactions;
  
  /**
   * Determines if the Graph implementations supports transactions.
   */
  public final Boolean supportsTransactions;
  
  /**
   * Gets the features related to graph sideEffects operation.
   */
  public final hydra.langs.tinkerpop.features.VariableFeatures variables;
  
  public GraphFeatures (Boolean supportsComputer, Boolean supportsConcurrentAccess, Boolean supportsIoRead, Boolean supportsIoWrite, Boolean supportsPersistence, Boolean supportsThreadedTransactions, Boolean supportsTransactions, hydra.langs.tinkerpop.features.VariableFeatures variables) {
    this.supportsComputer = supportsComputer;
    this.supportsConcurrentAccess = supportsConcurrentAccess;
    this.supportsIoRead = supportsIoRead;
    this.supportsIoWrite = supportsIoWrite;
    this.supportsPersistence = supportsPersistence;
    this.supportsThreadedTransactions = supportsThreadedTransactions;
    this.supportsTransactions = supportsTransactions;
    this.variables = variables;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof GraphFeatures)) {
      return false;
    }
    GraphFeatures o = (GraphFeatures) (other);
    return supportsComputer.equals(o.supportsComputer) && supportsConcurrentAccess.equals(o.supportsConcurrentAccess) && supportsIoRead.equals(o.supportsIoRead) && supportsIoWrite.equals(o.supportsIoWrite) && supportsPersistence.equals(o.supportsPersistence) && supportsThreadedTransactions.equals(o.supportsThreadedTransactions) && supportsTransactions.equals(o.supportsTransactions) && variables.equals(o.variables);
  }
  
  @Override
  public int hashCode() {
    return 2 * supportsComputer.hashCode() + 3 * supportsConcurrentAccess.hashCode() + 5 * supportsIoRead.hashCode() + 7 * supportsIoWrite.hashCode() + 11 * supportsPersistence.hashCode() + 13 * supportsThreadedTransactions.hashCode() + 17 * supportsTransactions.hashCode() + 19 * variables.hashCode();
  }
  
  public GraphFeatures withSupportsComputer(Boolean supportsComputer) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
  
  public GraphFeatures withSupportsConcurrentAccess(Boolean supportsConcurrentAccess) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
  
  public GraphFeatures withSupportsIoRead(Boolean supportsIoRead) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
  
  public GraphFeatures withSupportsIoWrite(Boolean supportsIoWrite) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
  
  public GraphFeatures withSupportsPersistence(Boolean supportsPersistence) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
  
  public GraphFeatures withSupportsThreadedTransactions(Boolean supportsThreadedTransactions) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
  
  public GraphFeatures withSupportsTransactions(Boolean supportsTransactions) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
  
  public GraphFeatures withVariables(hydra.langs.tinkerpop.features.VariableFeatures variables) {
    return new GraphFeatures(supportsComputer, supportsConcurrentAccess, supportsIoRead, supportsIoWrite, supportsPersistence, supportsThreadedTransactions, supportsTransactions, variables);
  }
}