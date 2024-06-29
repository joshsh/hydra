-- | See https://ossf.github.io/osv-schema

module Dev.Osv.Schema where

import qualified Hydra.Core as Core
import Data.List
import Data.Map
import Data.Set

data Credited = 
  Credited {
    creditedName :: String,
    creditedContact :: (Maybe [Url])}
  deriving (Eq, Ord, Read, Show)

_Credited = (Core.Name "dev/osv/schema.Credited")

_Credited_name = (Core.Name "name")

_Credited_contact = (Core.Name "contact")

-- | One of a limited set of defined ecosystems, currently Go, npm, OSS-Fuzz, PyPI, RubyGems, crates.io, Packagist, Maven, NuGet, Linux, Debian, Hex, Android, GitHub Actions, or Pub
newtype Ecosystem = 
  Ecosystem {
    -- | One of a limited set of defined ecosystems, currently Go, npm, OSS-Fuzz, PyPI, RubyGems, crates.io, Packagist, Maven, NuGet, Linux, Debian, Hex, Android, GitHub Actions, or Pub
    unEcosystem :: String}
  deriving (Eq, Ord, Read, Show)

_Ecosystem = (Core.Name "dev/osv/schema.Ecosystem")

data Entry = 
  Entry {
    -- | The default value is '1.0.0', matching version 1.0 of the OSV Schema
    entrySchemaVersion :: (Maybe OsvVersion),
    entryId :: Id,
    entryModified :: Timestamp,
    entryPublished :: (Maybe Timestamp),
    entryWithdrawn :: (Maybe Timestamp),
    entryAliases :: (Maybe [Id]),
    entryRelated :: (Maybe [Id]),
    entrySummary :: (Maybe String),
    entryDetails :: (Maybe Markdown),
    entrySeverity :: (Maybe [Severity]),
    entryAffected :: (Maybe [PackageVersions]),
    entryReferences :: (Maybe [Reference]),
    entryCredits :: (Maybe [Credited])}
  deriving (Eq, Ord, Read, Show)

_Entry = (Core.Name "dev/osv/schema.Entry")

_Entry_schemaVersion = (Core.Name "schemaVersion")

_Entry_id = (Core.Name "id")

_Entry_modified = (Core.Name "modified")

_Entry_published = (Core.Name "published")

_Entry_withdrawn = (Core.Name "withdrawn")

_Entry_aliases = (Core.Name "aliases")

_Entry_related = (Core.Name "related")

_Entry_summary = (Core.Name "summary")

_Entry_details = (Core.Name "details")

_Entry_severity = (Core.Name "severity")

_Entry_affected = (Core.Name "affected")

_Entry_references = (Core.Name "references")

_Entry_credits = (Core.Name "credits")

data Event = 
  EventIntroduced VersionOrZero |
  EventFixed Version |
  EventLastAffected Version |
  EventLimit VersionOrStar
  deriving (Eq, Ord, Read, Show)

_Event = (Core.Name "dev/osv/schema.Event")

_Event_introduced = (Core.Name "introduced")

_Event_fixed = (Core.Name "fixed")

_Event_lastAffected = (Core.Name "lastAffected")

_Event_limit = (Core.Name "limit")

-- | A string of the format <DB>-<ENTRYID>, where DB names the database and ENTRYID is in the format used by the database. For example: OSV-2020-111, CVE-2021-3114, or GHSA-vp9c-fpxx-744v
newtype Id = 
  Id {
    -- | A string of the format <DB>-<ENTRYID>, where DB names the database and ENTRYID is in the format used by the database. For example: OSV-2020-111, CVE-2021-3114, or GHSA-vp9c-fpxx-744v
    unId :: String}
  deriving (Eq, Ord, Read, Show)

_Id = (Core.Name "dev/osv/schema.Id")

-- | CommonMark markdown text
newtype Markdown = 
  Markdown {
    -- | CommonMark markdown text
    unMarkdown :: String}
  deriving (Eq, Ord, Read, Show)

_Markdown = (Core.Name "dev/osv/schema.Markdown")

-- | A string which follows the SemVer 2.0.0 format, with no leading 'v' prefix
newtype OsvVersion = 
  OsvVersion {
    -- | A string which follows the SemVer 2.0.0 format, with no leading 'v' prefix
    unOsvVersion :: String}
  deriving (Eq, Ord, Read, Show)

_OsvVersion = (Core.Name "dev/osv/schema.OsvVersion")

data Package = 
  Package {
    packageEcosystem :: Ecosystem,
    packageName :: String,
    packagePurl :: (Maybe Url)}
  deriving (Eq, Ord, Read, Show)

_Package = (Core.Name "dev/osv/schema.Package")

_Package_ecosystem = (Core.Name "ecosystem")

_Package_name = (Core.Name "name")

_Package_purl = (Core.Name "purl")

data PackageVersions = 
  PackageVersions {
    packageVersionsPackage :: Package,
    packageVersionsRanges :: (Maybe [VersionRange]),
    packageVersionsVersions :: (Maybe [Version])}
  deriving (Eq, Ord, Read, Show)

_PackageVersions = (Core.Name "dev/osv/schema.PackageVersions")

_PackageVersions_package = (Core.Name "package")

_PackageVersions_ranges = (Core.Name "ranges")

_PackageVersions_versions = (Core.Name "versions")

data Reference = 
  Reference {
    referenceType :: ReferenceType,
    referenceUrl :: Url}
  deriving (Eq, Ord, Read, Show)

_Reference = (Core.Name "dev/osv/schema.Reference")

_Reference_type = (Core.Name "type")

_Reference_url = (Core.Name "url")

-- | One of ADVISORY, ARTICLE, REPORT, FIX, GIT, PACKAGE, EVIDENCE, or WEB
newtype ReferenceType = 
  ReferenceType {
    -- | One of ADVISORY, ARTICLE, REPORT, FIX, GIT, PACKAGE, EVIDENCE, or WEB
    unReferenceType :: String}
  deriving (Eq, Ord, Read, Show)

_ReferenceType = (Core.Name "dev/osv/schema.ReferenceType")

data Severity = 
  Severity {
    severityType :: SeverityType,
    severityScore :: SeverityScore}
  deriving (Eq, Ord, Read, Show)

_Severity = (Core.Name "dev/osv/schema.Severity")

_Severity_type = (Core.Name "type")

_Severity_score = (Core.Name "score")

newtype SeverityScore = 
  SeverityScore {
    unSeverityScore :: String}
  deriving (Eq, Ord, Read, Show)

_SeverityScore = (Core.Name "dev/osv/schema.SeverityScore")

-- | The value CVSS_V3, or future supported types
newtype SeverityType = 
  SeverityType {
    -- | The value CVSS_V3, or future supported types
    unSeverityType :: String}
  deriving (Eq, Ord, Read, Show)

_SeverityType = (Core.Name "dev/osv/schema.SeverityType")

-- | An RFC3339-formatted timestamp in UTC (ending in 'Z')
newtype Timestamp = 
  Timestamp {
    -- | An RFC3339-formatted timestamp in UTC (ending in 'Z')
    unTimestamp :: String}
  deriving (Eq, Ord, Read, Show)

_Timestamp = (Core.Name "dev/osv/schema.Timestamp")

newtype Url = 
  Url {
    unUrl :: String}
  deriving (Eq, Ord, Read, Show)

_Url = (Core.Name "dev/osv/schema.Url")

-- | A version number in an ecosystem-specific format
newtype Version = 
  Version {
    -- | A version number in an ecosystem-specific format
    unVersion :: String}
  deriving (Eq, Ord, Read, Show)

_Version = (Core.Name "dev/osv/schema.Version")

-- | An ecosystem-specific version number, or the string '*' representing infinity
newtype VersionOrStar = 
  VersionOrStar {
    -- | An ecosystem-specific version number, or the string '*' representing infinity
    unVersionOrStar :: String}
  deriving (Eq, Ord, Read, Show)

_VersionOrStar = (Core.Name "dev/osv/schema.VersionOrStar")

-- | An ecosystem-specific version number, or the string '0' representing a version that sorts before any other version
newtype VersionOrZero = 
  VersionOrZero {
    -- | An ecosystem-specific version number, or the string '0' representing a version that sorts before any other version
    unVersionOrZero :: String}
  deriving (Eq, Ord, Read, Show)

_VersionOrZero = (Core.Name "dev/osv/schema.VersionOrZero")

data VersionRange = 
  VersionRange {
    versionRangeType :: VersionType,
    versionRangeRepo :: (Maybe Url),
    versionRangeEvents :: [Event]}
  deriving (Eq, Ord, Read, Show)

_VersionRange = (Core.Name "dev/osv/schema.VersionRange")

_VersionRange_type = (Core.Name "type")

_VersionRange_repo = (Core.Name "repo")

_VersionRange_events = (Core.Name "events")

-- | One of the values 'SEMVER', 'ECOSYSTEM', or 'GIT
newtype VersionType = 
  VersionType {
    -- | One of the values 'SEMVER', 'ECOSYSTEM', or 'GIT
    unVersionType :: String}
  deriving (Eq, Ord, Read, Show)

_VersionType = (Core.Name "dev/osv/schema.VersionType")
