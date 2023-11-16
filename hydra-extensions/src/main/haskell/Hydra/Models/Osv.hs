module Hydra.Models.Osv where

import Hydra.Sources.Tier4.All
import Hydra.Dsl.Types as Types
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Annotations


-- Note: database_specific and ecosystem_specific fields are ignored, though they must be tolerated when reading entry JSON
osvSchemaModule :: Module
osvSchemaModule = Module ns elements [] $
    Just "See https://ossf.github.io/osv-schema"
  where
    ns = Namespace "dev/osv/schema"
    def = datatype ns
    osv = typeref ns

    elements = [

      def "Credited" $
        record [
          "name">: string,
          "contact">: optional $ list $ osv "Url"],

      def "Ecosystem" $
        doc ("One of a limited set of defined ecosystems, currently "
          ++ "Go, npm, OSS-Fuzz, PyPI, RubyGems, crates.io, Packagist, Maven, NuGet, Linux, Debian, Hex, Android, GitHub Actions, or Pub")
        string,

      def "Entry" $
        record [
          "schemaVersion">:
            doc "The default value is '1.0.0', matching version 1.0 of the OSV Schema" $
            optional $ osv "OsvVersion",
          "id">: osv "Id",
          "modified">: osv "Timestamp",
          "published">: optional $ osv "Timestamp",
          "withdrawn">: optional $ osv "Timestamp",
          "aliases">: optional $ list $ osv "Id",
          "related">: optional $ list $ osv "Id",
          "summary">: optional string,
          "details">: optional $ osv "Markdown",
          "severity">: optional $ list $ osv "Severity",
          "affected">: optional  $ list $ osv "PackageVersions",
          "references">: optional $ list $ osv "Reference",
          "credits">: optional $ list $ osv "Credited"],

      def "Event" $
        union [
          "introduced">: osv "VersionOrZero",
          "fixed">: osv "Version",
          "lastAffected">: osv "Version",
          "limit">: osv "VersionOrStar"],

      def "Id" $
        doc ("A string of the format <DB>-<ENTRYID>, where DB names the database and ENTRYID is in the format used "
          ++ "by the database. For example: OSV-2020-111, CVE-2021-3114, or GHSA-vp9c-fpxx-744v")
        string,

      def "Markdown" $
        doc "CommonMark markdown text"
        string,

      def "OsvVersion" $
        doc "A string which follows the SemVer 2.0.0 format, with no leading 'v' prefix"
        string,

      def "Package" $
        record [
          "ecosystem">: osv "Ecosystem",
          "name">: string,
          "purl">: optional $ osv "Url"],

      def "PackageVersions" $
        record [
          "package">: osv "Package",
          "ranges">: optional $ list $ osv "VersionRange",
          "versions">: optional $ list $ osv "Version"],

      def "Reference" $
        record [
          "type">: osv "ReferenceType",
          "url">: osv "Url"],

      def "ReferenceType" $
        doc "One of ADVISORY, ARTICLE, REPORT, FIX, GIT, PACKAGE, EVIDENCE, or WEB"
        string,

      def "Severity" $
        record [
          "type">: osv "SeverityType",
          "score">: osv "SeverityScore"],

      def "SeverityScore" string,

      def "SeverityType" $
        doc "The value CVSS_V3, or future supported types"
        string,

      def "Timestamp" $
        doc "An RFC3339-formatted timestamp in UTC (ending in 'Z')"
        string,

      def "Url" string,

      def "Version" $
        doc "A version number in an ecosystem-specific format"
        string,

      def "VersionOrStar" $
        doc "An ecosystem-specific version number, or the string '*' representing infinity"
        string,

      def "VersionOrZero" $
        doc "An ecosystem-specific version number, or the string '0' representing a version that sorts before any other version"
        string,

      def "VersionRange" $
        record [
          "type">: osv "VersionType",
          "repo">: optional $ osv "Url",
          "events">: list $ osv "Event"],

      def "VersionType" $
        doc "One of the values 'SEMVER', 'ECOSYSTEM', or 'GIT"
        string]
