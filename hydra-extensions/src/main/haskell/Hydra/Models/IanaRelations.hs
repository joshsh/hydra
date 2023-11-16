module Hydra.Models.IanaRelations where

import Hydra.Sources.Tier4.All
import Hydra.Dsl.Types as Types
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Annotations


ianaRelationsModule :: Module
ianaRelationsModule = Module ns elements [] $
    Just ("All IANA Link Relation Types, as of 2022-10-11. " ++
          "See https://www.iana.org/assignments/link-relations/link-relations.xhtml")
  where
    ns = Namespace "org/iana/linkrelations"
    def = datatype ns

    elements = [
      def "LinkRelationType" $
        doc "An IANA link relation type" $
        union [
          "about">:
            doc ("Refers to a resource that is the subject of the link's context. [RFC6903], section 2") unit,
          "acl">:
            doc ("Asserts that the link target provides an access control resource for the link context. [https://solidproject.org/TR/wac#acl-link-relation]") unit,
          "alternate">:
            doc ("Refers to a substitute for this context [HTML]") unit,
          "amphtml">:
            doc ("Used to reference alternative content that uses the AMP profile of the HTML format. [AMP HTML]") unit,
          "appendix">:
            doc ("Refers to an appendix. [HTML 4.01 Specification]") unit,
          "apple-touch-icon">:
            doc ("Refers to an icon for the context. Synonym for icon. [Configuring Web Applications]") unit,
          "apple-touch-startup-image">:
            doc ("Refers to a launch screen for the context. [Configuring Web Applications]") unit,
          "archives">:
            doc ("Refers to a collection of records, documents, or other materials of historical interest. [HTML5]") unit,
          "author">:
            doc ("Refers to the context's author. [HTML]") unit,
          "blocked-by">:
            doc ("Identifies the entity that blocks access to a resource following receipt of a legal demand. [RFC7725]") unit,
          "bookmark">:
            doc ("Gives a permanent link to use for bookmarking purposes. [HTML]") unit,
          "canonical">:
            doc ("Designates the preferred version of a resource (the IRI and its contents). [RFC6596]") unit,
          "chapter">:
            doc ("Refers to a chapter in a collection of resources. [HTML 4.01 Specification]") unit,
          "cite-as">:
            doc ("Indicates that the link target is preferred over the link context for the purpose of permanent citation. [RFC8574]") unit,
          "collection">:
            doc ("The target IRI points to a resource which represents the collection resource for the context IRI. [RFC6573]") unit,
          "contents">:
            doc ("Refers to a table of contents. [HTML 4.01 Specification]") unit,
          "convertedfrom">:
            doc ("The document linked to was later converted to the document that contains this link relation. For example, an RFC can have a link to the Internet-Draft that became the RFC; in that case, the link relation would be \"convertedFrom\". [RFC7991] This relation is different than \"predecessor-version\" in that \"predecessor-version\" is for items in a version control system. It is also different than \"previous\" in that this relation is used for converted resources, not those that are part of a sequence of resources.") unit,
          "copyright">:
            doc ("Refers to a copyright statement that applies to the link's context. [HTML 4.01 Specification]") unit,
          "create-form">:
            doc ("The target IRI points to a resource where a submission form can be obtained. [RFC6861]") unit,
          "current">:
            doc ("Refers to a resource containing the most recent item(s) in a collection of resources. [RFC5005]") unit,
          "describedby">:
            doc ("Refers to a resource providing information about the link's context. [Protocol for Web Description Resources (POWDER)]") unit,
          "describes">:
            doc ("The relationship A 'describes' B asserts that resource A provides a description of resource B. There are no constraints on the format or representation of either A or B, neither are there any further constraints on either resource. [RFC6892] This link relation type is the inverse of the 'describedby' relation type. While 'describedby' establishes a relation from the described resource back to the resource that describes it, 'describes' established a relation from the describing resource to the resource it describes. If B is 'describedby' A, then A 'describes' B.") unit,
          "disclosure">:
            doc ("Refers to a list of patent disclosures made with respect to material for which 'disclosure' relation is specified. [RFC6579]") unit,
          "dns-prefetch">:
            doc ("Used to indicate an origin that will be used to fetch required resources for the link context, and that the user agent ought to resolve as early as possible. [Resource Hints]") unit,
          "duplicate">:
            doc ("Refers to a resource whose available representations are byte-for-byte identical with the corresponding representations of the context IRI. [RFC6249] This relation is for static resources. That is, an HTTP GET request on any duplicate will return the same representation. It does not make sense for dynamic or POSTable resources and should not be used for them.") unit,
          "edit">:
            doc ("Refers to a resource that can be used to edit the link's context. [RFC5023]") unit,
          "edit-form">:
            doc ("The target IRI points to a resource where a submission form for editing associated resource can be obtained. [RFC6861]") unit,
          "edit-media">:
            doc ("Refers to a resource that can be used to edit media associated with the link's context. [RFC5023]") unit,
          "enclosure">:
            doc ("Identifies a related resource that is potentially large and might require special handling. [RFC4287]") unit,
          "external">:
            doc ("Refers to a resource that is not part of the same site as the current context. [HTML]") unit,
          "first">:
            doc ("An IRI that refers to the furthest preceding resource in a series of resources. [RFC8288] This relation type registration did not indicate a reference. Originally requested by Mark Nottingham in December 2004.") unit,
          "glossary">:
            doc ("Refers to a glossary of terms. [HTML 4.01 Specification]") unit,
          "help">:
            doc ("Refers to context-sensitive help. [HTML]") unit,
          "hosts">:
            doc ("Refers to a resource hosted by the server indicated by the link context. [RFC6690] This relation is used in CoRE where links are retrieved as a \"/.well-known/core\" resource representation, and is the default relation type in the CoRE Link Format.") unit,
          "hub">:
            doc ("Refers to a hub that enables registration for notification of updates to the context. [WebSub] This relation type was requested by Brett Slatkin.") unit,
          "icon">:
            doc ("Refers to an icon representing the link's context. [HTML]") unit,
          "index">:
            doc ("Refers to an index. [HTML 4.01 Specification]") unit,
          "intervalafter">:
            doc ("refers to a resource associated with a time interval that ends before the beginning of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.21") unit,
          "intervalbefore">:
            doc ("refers to a resource associated with a time interval that begins after the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.22") unit,
          "intervalcontains">:
            doc ("refers to a resource associated with a time interval that begins after the beginning of the time interval associated with the context resource, and ends before the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.23") unit,
          "intervaldisjoint">:
            doc ("refers to a resource associated with a time interval that begins after the end of the time interval associated with the context resource, or ends before the beginning of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.24") unit,
          "intervalduring">:
            doc ("refers to a resource associated with a time interval that begins before the beginning of the time interval associated with the context resource, and ends after the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.25") unit,
          "intervalequals">:
            doc ("refers to a resource associated with a time interval whose beginning coincides with the beginning of the time interval associated with the context resource, and whose end coincides with the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.26") unit,
          "intervalfinishedby">:
            doc ("refers to a resource associated with a time interval that begins after the beginning of the time interval associated with the context resource, and whose end coincides with the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.27") unit,
          "intervalfinishes">:
            doc ("refers to a resource associated with a time interval that begins before the beginning of the time interval associated with the context resource, and whose end coincides with the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.28") unit,
          "intervalin">:
            doc ("refers to a resource associated with a time interval that begins before or is coincident with the beginning of the time interval associated with the context resource, and ends after or is coincident with the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.29") unit,
          "intervalmeets">:
            doc ("refers to a resource associated with a time interval whose beginning coincides with the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.30") unit,
          "intervalmetby">:
            doc ("refers to a resource associated with a time interval whose end coincides with the beginning of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.31") unit,
          "intervaloverlappedby">:
            doc ("refers to a resource associated with a time interval that begins before the beginning of the time interval associated with the context resource, and ends after the beginning of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.32") unit,
          "intervaloverlaps">:
            doc ("refers to a resource associated with a time interval that begins before the end of the time interval associated with the context resource, and ends after the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.33") unit,
          "intervalstartedby">:
            doc ("refers to a resource associated with a time interval whose beginning coincides with the beginning of the time interval associated with the context resource, and ends before the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.34") unit,
          "intervalstarts">:
            doc ("refers to a resource associated with a time interval whose beginning coincides with the beginning of the time interval associated with the context resource, and ends after the end of the time interval associated with the context resource [Time Ontology in OWL] section 4.2.35") unit,
          "item">:
            doc ("The target IRI points to a resource that is a member of the collection represented by the context IRI. [RFC6573]") unit,
          "last">:
            doc ("An IRI that refers to the furthest following resource in a series of resources. [RFC8288] This relation type registration did not indicate a reference. Originally requested by Mark Nottingham in December 2004.") unit,
          "latest-version">:
            doc ("Points to a resource containing the latest (e.g., current) version of the context. [RFC5829]") unit,
          "license">:
            doc ("Refers to a license associated with this context. [RFC4946] For implications of use in HTML, see: http://www.w3.org/TR/html5/links.html#link-type-license") unit,
          "linkset">:
            doc ("The link target of a link with the \"linkset\" relation type provides a set of links, including links in which the link context of the link participates. [RFC9264]") unit,
          "lrdd">:
            doc ("Refers to further information about the link's context, expressed as a LRDD (\"Link-based Resource Descriptor Document\") resource. See [RFC6415] for information about processing this relation type in host-meta documents. When used elsewhere, it refers to additional links and other metadata. Multiple instances indicate additional LRDD resources. LRDD resources MUST have an \"application/xrd+xml\" representation, and MAY have others. [RFC6415]") unit,
          "manifest">:
            doc ("Links to a manifest file for the context. [Web App Manifest]") unit,
          "mask-icon">:
            doc ("Refers to a mask that can be applied to the icon for the context. [Creating Pinned Tab Icons]") unit,
          "media-feed">:
            doc ("Refers to a feed of personalised media recommendations relevant to the link context. [https://wicg.github.io/media-feeds/#discovery-of-media-feeds]") unit,
          "memento">:
            doc ("The Target IRI points to a Memento, a fixed resource that will not change state anymore. [RFC7089] A Memento for an Original Resource is a resource that encapsulates a prior state of the Original Resource.") unit,
          "micropub">:
            doc ("Links to the context's Micropub endpoint. [Micropub]") unit,
          "modulepreload">:
            doc ("Refers to a module that the user agent is to preemptively fetch and store for use in the current context. [HTML]") unit,
          "monitor">:
            doc ("Refers to a resource that can be used to monitor changes in an HTTP resource. [RFC5989]") unit,
          "monitor-group">:
            doc ("Refers to a resource that can be used to monitor changes in a specified group of HTTP resources. [RFC5989]") unit,
          "next">:
            doc ("Indicates that the link's context is a part of a series, and that the next in the series is the link target. [HTML]") unit,
          "next-archive">:
            doc ("Refers to the immediately following archive resource. [RFC5005]") unit,
          "nofollow">:
            doc ("Indicates that the context’s original author or publisher does not endorse the link target. [HTML]") unit,
          "noopener">:
            doc ("Indicates that any newly created top-level browsing context which results from following the link will not be an auxiliary browsing context. [HTML]") unit,
          "noreferrer">:
            doc ("Indicates that no referrer information is to be leaked when following the link. [HTML]") unit,
          "opener">:
            doc ("Indicates that any newly created top-level browsing context which results from following the link will be an auxiliary browsing context. [HTML]") unit,
          "openid2.local_id">:
            doc ("Refers to an OpenID Authentication server on which the context relies for an assertion that the end user controls an Identifier. [OpenID Authentication 2.0 - Final]") unit,
          "openid2.provider">:
            doc ("Refers to a resource which accepts OpenID Authentication protocol messages for the context. [OpenID Authentication 2.0 - Final]") unit,
          "original">:
            doc ("The Target IRI points to an Original Resource. [RFC7089] An Original Resource is a resource that exists or used to exist, and for which access to one of its prior states may be required.") unit,
          "p3pv1">:
            doc ("Refers to a P3P privacy policy for the context. [The Platform for Privacy Preferences 1.0 (P3P1.0) Specification]") unit,
          "payment">:
            doc ("Indicates a resource where payment is accepted. [RFC8288] This relation type registration did not indicate a reference. Requested by Joshua Kinberg and Robert Sayre. It is meant as a general way to facilitate acts of payment, and thus this specification makes no assumptions on the type of payment or transaction protocol. Examples may include a web page where donations are accepted or where goods and services are available for purchase. rel=\"payment\" is not intended to initiate an automated transaction. In Atom documents, a link element with a rel=\"payment\" attribute may exist at the feed/channel level and/or the entry/item level. For example, a rel=\"payment\" link at the feed/channel level may point to a \"tip jar\" URI, whereas an entry/ item containing a book review may include a rel=\"payment\" link that points to the location where the book may be purchased through an online retailer.") unit,
          "pingback">:
            doc ("Gives the address of the pingback resource for the link context. [Pingback 1.0]") unit,
          "preconnect">:
            doc ("Used to indicate an origin that will be used to fetch required resources for the link context. Initiating an early connection, which includes the DNS lookup, TCP handshake, and optional TLS negotiation, allows the user agent to mask the high latency costs of establishing a connection. [Resource Hints]") unit,
          "predecessor-version">:
            doc ("Points to a resource containing the predecessor version in the version history. [RFC5829]") unit,
          "prefetch">:
            doc ("The prefetch link relation type is used to identify a resource that might be required by the next navigation from the link context, and that the user agent ought to fetch, such that the user agent can deliver a faster response once the resource is requested in the future. [Resource Hints]") unit,
          "preload">:
            doc ("Refers to a resource that should be loaded early in the processing of the link's context, without blocking rendering. [Preload] Additional target attributes establish the detailed fetch properties of the link.") unit,
          "prerender">:
            doc ("Used to identify a resource that might be required by the next navigation from the link context, and that the user agent ought to fetch and execute, such that the user agent can deliver a faster response once the resource is requested in the future. [Resource Hints]") unit,
          "prev">:
            doc ("Indicates that the link's context is a part of a series, and that the previous in the series is the link target. [HTML]") unit,
          "preview">:
            doc ("Refers to a resource that provides a preview of the link's context. [RFC6903], section 3") unit,
          "previous">:
            doc ("Refers to the previous resource in an ordered series of resources. Synonym for \"prev\". [HTML 4.01 Specification]") unit,
          "prev-archive">:
            doc ("Refers to the immediately preceding archive resource. [RFC5005]") unit,
          "privacy-policy">:
            doc ("Refers to a privacy policy associated with the link's context. [RFC6903], section 4") unit,
          "profile">:
            doc ("Identifying that a resource representation conforms to a certain profile, without affecting the non-profile semantics of the resource representation. [RFC6906] Profile URIs are primarily intended to be used as identifiers, and thus clients SHOULD NOT indiscriminately access profile URIs.") unit,
          "publication">:
            doc ("Links to a publication manifest. A manifest represents structured information about a publication, such as informative metadata, a list of resources, and a default reading order. [Publication Manifest]") unit,
          "related">:
            doc ("Identifies a related resource. [RFC4287]") unit,
          "restconf">:
            doc ("Identifies the root of RESTCONF API as configured on this HTTP server. The \"restconf\" relation defines the root of the API defined in RFC8040. Subsequent revisions of RESTCONF will use alternate relation values to support protocol versioning. [RFC8040]") unit,
          "replies">:
            doc ("Identifies a resource that is a reply to the context of the link. [RFC4685]") unit,
          "ruleinput">:
            doc ("The resource identified by the link target provides an input value to an instance of a rule, where the resource which represents the rule instance is identified by the link context. [OCF Core Optional 2.2.0]") unit,
          "search">:
            doc ("Refers to a resource that can be used to search through the link's context and related resources. [OpenSearch]") unit,
          "section">:
            doc ("Refers to a section in a collection of resources. [HTML 4.01 Specification]") unit,
          "self">:
            doc ("Conveys an identifier for the link's context. [RFC4287]") unit,
          "service">:
            doc ("Indicates a URI that can be used to retrieve a service document. [RFC5023] When used in an Atom document, this relation type specifies Atom Publishing Protocol service documents by default. Requested by James Snell.") unit,
          "service-desc">:
            doc ("Identifies service description for the context that is primarily intended for consumption by machines. [RFC8631]") unit,
          "service-doc">:
            doc ("Identifies service documentation for the context that is primarily intended for human consumption. [RFC8631]") unit,
          "service-meta">:
            doc ("Identifies general metadata for the context that is primarily intended for consumption by machines. [RFC8631]") unit,
          "siptrunkingcapability">:
            doc ("refers to a capability document that defines parameters or configuration requirements for automated peering and communication channel negotiation of the Session Initiation Protocol (SIP). [draft-engi-siptrunkingcapability-link]") unit,
          "sponsored">:
            doc ("Refers to a resource that is within a context that is sponsored (such as advertising or another compensation agreement). [Google Blog post 09-2019]") unit,
          "start">:
            doc ("Refers to the first resource in a collection of resources. [HTML 4.01 Specification]") unit,
          "status">:
            doc ("Identifies a resource that represents the context's status. [RFC8631]") unit,
          "stylesheet">:
            doc ("Refers to a stylesheet. [HTML]") unit,
          "subsection">:
            doc ("Refers to a resource serving as a subsection in a collection of resources. [HTML 4.01 Specification]") unit,
          "successor-version">:
            doc ("Points to a resource containing the successor version in the version history. [RFC5829]") unit,
          "sunset">:
            doc ("Identifies a resource that provides information about the context's retirement policy. [RFC8594]") unit,
          "tag">:
            doc ("Gives a tag (identified by the given address) that applies to the current document. [HTML]") unit,
          "terms-of-service">:
            doc ("Refers to the terms of service associated with the link's context. [RFC6903], section 5") unit,
          "timegate">:
            doc ("The Target IRI points to a TimeGate for an Original Resource. [RFC7089] A TimeGate for an Original Resource is a resource that is capable of datetime negotiation to support access to prior states of the Original Resource.") unit,
          "timemap">:
            doc ("The Target IRI points to a TimeMap for an Original Resource. [RFC7089] A TimeMap for an Original Resource is a resource from which a list of URIs of Mementos of the Original Resource is available.") unit,
          "type">:
            doc ("Refers to a resource identifying the abstract semantic type of which the link's context is considered to be an instance. [RFC6903], section 6") unit,
          "ugc">:
            doc ("Refers to a resource that is within a context that is User Generated Content. [Google Blog post 09-2019]") unit,
          "up">:
            doc ("Refers to a parent document in a hierarchy of documents. [RFC8288] This relation type registration did not indicate a reference. Requested by Noah Slater.") unit,
          "version-history">:
            doc ("Points to a resource containing the version history for the context. [RFC5829]") unit,
          "via">:
            doc ("Identifies a resource that is the source of the information in the link's context. [RFC4287]") unit,
          "webmention">:
            doc ("Identifies a target URI that supports the Webmention protocol. This allows clients that mention a resource in some form of publishing process to contact that endpoint and inform it that this resource has been mentioned. [Webmention] This is a similar \"Linkback\" mechanism to the ones of Refback, Trackback, and Pingback. It uses a different protocol, though, and thus should be discoverable through its own link relation type.") unit,
          "working-copy">:
            doc ("Points to a working copy for this resource. [RFC5829]") unit,
          "working-copy-of">:
            doc ("Points to the versioned resource from which this working copy was obtained. [RFC5829]") unit]]
