// Note: this is an automatically generated file. Do not edit.

package hydra.langs.cypher.features;

import java.io.Serializable;

/**
 * A set of features for projections.
 */
public class ProjectionFeatures implements Serializable {
  public static final hydra.core.Name NAME = new hydra.core.Name("hydra/langs/cypher/features.ProjectionFeatures");
  
  /**
   * Whether to expect the LIMIT clause.
   */
  public final Boolean limit;
  
  /**
   * Whether to expect the ORDER BY clause.
   */
  public final Boolean orderBy;
  
  /**
   * Whether to expect the DISTINCT keyword.
   */
  public final Boolean projectDistinct;
  
  /**
   * Whether to expect the * projection.
   */
  public final Boolean projectAll;
  
  /**
   * Whether to expect the AS keyword.
   */
  public final Boolean projectAs;
  
  /**
   * Whether to expect the SKIP clause.
   */
  public final Boolean skip;
  
  /**
   * Whether to expect the ASC/ASCENDING and DESC/DESCENDING keywords.
   */
  public final Boolean sortOrder;
  
  public ProjectionFeatures (Boolean limit, Boolean orderBy, Boolean projectDistinct, Boolean projectAll, Boolean projectAs, Boolean skip, Boolean sortOrder) {
    java.util.Objects.requireNonNull((limit));
    java.util.Objects.requireNonNull((orderBy));
    java.util.Objects.requireNonNull((projectDistinct));
    java.util.Objects.requireNonNull((projectAll));
    java.util.Objects.requireNonNull((projectAs));
    java.util.Objects.requireNonNull((skip));
    java.util.Objects.requireNonNull((sortOrder));
    this.limit = limit;
    this.orderBy = orderBy;
    this.projectDistinct = projectDistinct;
    this.projectAll = projectAll;
    this.projectAs = projectAs;
    this.skip = skip;
    this.sortOrder = sortOrder;
  }
  
  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ProjectionFeatures)) {
      return false;
    }
    ProjectionFeatures o = (ProjectionFeatures) (other);
    return limit.equals(o.limit) && orderBy.equals(o.orderBy) && projectDistinct.equals(o.projectDistinct) && projectAll.equals(o.projectAll) && projectAs.equals(o.projectAs) && skip.equals(o.skip) && sortOrder.equals(o.sortOrder);
  }
  
  @Override
  public int hashCode() {
    return 2 * limit.hashCode() + 3 * orderBy.hashCode() + 5 * projectDistinct.hashCode() + 7 * projectAll.hashCode() + 11 * projectAs.hashCode() + 13 * skip.hashCode() + 17 * sortOrder.hashCode();
  }
  
  public ProjectionFeatures withLimit(Boolean limit) {
    java.util.Objects.requireNonNull((limit));
    return new ProjectionFeatures(limit, orderBy, projectDistinct, projectAll, projectAs, skip, sortOrder);
  }
  
  public ProjectionFeatures withOrderBy(Boolean orderBy) {
    java.util.Objects.requireNonNull((orderBy));
    return new ProjectionFeatures(limit, orderBy, projectDistinct, projectAll, projectAs, skip, sortOrder);
  }
  
  public ProjectionFeatures withProjectDistinct(Boolean projectDistinct) {
    java.util.Objects.requireNonNull((projectDistinct));
    return new ProjectionFeatures(limit, orderBy, projectDistinct, projectAll, projectAs, skip, sortOrder);
  }
  
  public ProjectionFeatures withProjectAll(Boolean projectAll) {
    java.util.Objects.requireNonNull((projectAll));
    return new ProjectionFeatures(limit, orderBy, projectDistinct, projectAll, projectAs, skip, sortOrder);
  }
  
  public ProjectionFeatures withProjectAs(Boolean projectAs) {
    java.util.Objects.requireNonNull((projectAs));
    return new ProjectionFeatures(limit, orderBy, projectDistinct, projectAll, projectAs, skip, sortOrder);
  }
  
  public ProjectionFeatures withSkip(Boolean skip) {
    java.util.Objects.requireNonNull((skip));
    return new ProjectionFeatures(limit, orderBy, projectDistinct, projectAll, projectAs, skip, sortOrder);
  }
  
  public ProjectionFeatures withSortOrder(Boolean sortOrder) {
    java.util.Objects.requireNonNull((sortOrder));
    return new ProjectionFeatures(limit, orderBy, projectDistinct, projectAll, projectAs, skip, sortOrder);
  }
}