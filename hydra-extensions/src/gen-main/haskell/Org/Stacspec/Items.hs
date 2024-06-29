-- | A model for SpatioTemporal Asset Catalog (STAC) Items. See https://github.com/radiantearth/stac-spec/blob/master/item-spec/item-spec.md

module Org.Stacspec.Items where

import qualified Hydra.Core as Core
import qualified Org.Geojson.Model as Model
import qualified Org.Iana.Linkrelations as Linkrelations
import Data.List
import Data.Map
import Data.Set

-- | An Asset is an object that contains a URI to data associated with the Item that can be downloaded or streamed. It is allowed to add additional fields.
data Asset = 
  Asset {
    -- | URI to the asset object. Relative and absolute URI are both allowed.
    assetHref :: Uri,
    -- | The displayed title for clients and users.
    assetTitle :: (Maybe String),
    -- | A description of the Asset providing additional details, such as how it was processed or created. CommonMark 0.29 syntax MAY be used for rich text representation.
    assetDescription :: (Maybe String),
    -- | Media type of the asset. See the common media types in the best practice doc for commonly used asset types.
    assetType :: (Maybe MediaType),
    -- | The semantic roles of the asset, similar to the use of rel in links.
    assetRoles :: [Role]}
  deriving (Eq, Ord, Read, Show)

_Asset = (Core.Name "org/stacspec/items.Asset")

_Asset_href = (Core.Name "href")

_Asset_title = (Core.Name "title")

_Asset_description = (Core.Name "description")

_Asset_type = (Core.Name "type")

_Asset_roles = (Core.Name "roles")

-- | This object describes a STAC Item. The fields id, type, bbox, geometry and properties are inherited from GeoJSON.
data Item = 
  Item {
    itemFeature :: Model.Feature,
    -- | The STAC version the Item implements
    itemStacVersion :: StacVersion,
    -- | A list of extensions the Item implements
    itemStacExtensions :: [Url],
    -- | List of link objects to resources and related URLs. A link with the rel set to self is strongly recommended.
    itemLinks :: [Link],
    -- | Dictionary of asset objects that can be downloaded, each with a unique key.
    itemAssets :: (Map String Asset),
    -- | The id of the STAC Collection this Item references to (see collection relation type). This field is required if such a relation type is present and is not allowed otherwise. This field provides an easy way for a user to search for any Items that belong in a specified Collection. Must be a non-empty string.
    itemCollection :: (Maybe Model.Id)}
  deriving (Eq, Ord, Read, Show)

_Item = (Core.Name "org/stacspec/items.Item")

_Item_feature = (Core.Name "feature")

_Item_stacVersion = (Core.Name "stacVersion")

_Item_stacExtensions = (Core.Name "stacExtensions")

_Item_links = (Core.Name "links")

_Item_assets = (Core.Name "assets")

_Item_collection = (Core.Name "collection")

-- | This object describes a relationship with another entity. Data providers are advised to be liberal with the links section, to describe things like the Catalog an Item is in, related Items, parent or child Items (modeled in different ways, like an 'acquisition' or derived data). It is allowed to add additional fields such as a title and type.
data Link = 
  Link {
    -- | The actual link in the format of an URL. Relative and absolute links are both allowed.
    linkHref :: Url,
    -- | Relationship between the current document and the linked document. See chapter "Relation types" for more information.
    linkRel :: RelationType,
    -- | Media type of the referenced entity.
    linkType :: (Maybe MediaType),
    -- | A human readable title to be used in rendered displays of the link.
    linkTitle :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Link = (Core.Name "org/stacspec/items.Link")

_Link_href = (Core.Name "href")

_Link_rel = (Core.Name "rel")

_Link_type = (Core.Name "type")

_Link_title = (Core.Name "title")

newtype MediaType = 
  MediaType {
    unMediaType :: String}
  deriving (Eq, Ord, Read, Show)

_MediaType = (Core.Name "org/stacspec/items.MediaType")

-- | STAC Items use a variety of rel types in the link object, to describe the exact nature of the link between this Item and the entity it is linking to. It is recommended to use the official IANA Link Relation Types where possible. The following table explains places where STAC use custom rel types are used with Items. This happens where there is not a clear official option, or where STAC uses an official type but adds additional meaning for the STAC context.
data RelationType = 
  RelationTypeIana Linkrelations.LinkRelationType |
  RelationTypeStac StacRelationType |
  RelationTypeOther String
  deriving (Eq, Ord, Read, Show)

_RelationType = (Core.Name "org/stacspec/items.RelationType")

_RelationType_iana = (Core.Name "iana")

_RelationType_stac = (Core.Name "stac")

_RelationType_other = (Core.Name "other")

-- | The roles field is used to describe the purpose of each asset. It is recommended to include one for every asset, to give users a sense of why they might want to make use of the asset. There are some emerging standards that enable clients to take particular action when they encounter particular roles, listed below. But implementors are encouraged to come up with their own terms to describe the role.
data Role = 
  -- | An asset that represents a thumbnail of the Item, typically a true color image (for Items with assets in the visible wavelengths), lower-resolution (typically smaller 600x600 pixels), and typically a JPEG or PNG (suitable for display in a web browser). Multiple assets may have this purpose, but it recommended that the type and roles be unique tuples. For example, Sentinel-2 L2A provides thumbnail images in both JPEG and JPEG2000 formats, and would be distinguished by their media types.
  RoleThumbnail  |
  -- | An asset that represents a possibly larger view than the thumbnail of the Item, for example, a true color composite of multi-band data.
  RoleOverview  |
  -- | The data itself. This is a suggestion for a common role for data files to be used in case data providers don't come up with their own names and semantics.
  RoleData  |
  -- | A metadata sidecar file describing the data in this Item, for example the Landsat-8 MTL file.
  RoleMetadata  |
  RoleOther String
  deriving (Eq, Ord, Read, Show)

_Role = (Core.Name "org/stacspec/items.Role")

_Role_thumbnail = (Core.Name "thumbnail")

_Role_overview = (Core.Name "overview")

_Role_data = (Core.Name "data")

_Role_metadata = (Core.Name "metadata")

_Role_other = (Core.Name "other")

data StacRelationType = 
  -- | STRONGLY RECOMMENDED. Absolute URL to the Item if it is available at a public URL. This is particularly useful when in a download package that includes metadata, so that the downstream user can know where the data has come from.
  StacRelationTypeSelf  |
  -- | URL to the root STAC entity (Catalog or Collection).
  StacRelationTypeRoot  |
  -- | URL to the parent STAC entity (Catalog or Collection).
  StacRelationTypeParent  |
  -- | STRONGLY RECOMMENDED. URL to a Collection. Absolute URLs should be used whenever possible. The referenced Collection is STRONGLY RECOMMENDED to implement the same STAC version as the Item. A link with this rel type is required if the collection field in properties is present.
  StacRelationTypeCollection  |
  -- | URL to a STAC Item that was used as input data in the creation of this Item.
  StacRelationTypeDerivedFrom 
  deriving (Eq, Ord, Read, Show)

_StacRelationType = (Core.Name "org/stacspec/items.StacRelationType")

_StacRelationType_self = (Core.Name "self")

_StacRelationType_root = (Core.Name "root")

_StacRelationType_parent = (Core.Name "parent")

_StacRelationType_collection = (Core.Name "collection")

_StacRelationType_derivedFrom = (Core.Name "derivedFrom")

newtype StacVersion = 
  StacVersion {
    unStacVersion :: String}
  deriving (Eq, Ord, Read, Show)

_StacVersion = (Core.Name "org/stacspec/items.StacVersion")

newtype Uri = 
  Uri {
    unUri :: String}
  deriving (Eq, Ord, Read, Show)

_Uri = (Core.Name "org/stacspec/items.Uri")

newtype Url = 
  Url {
    unUrl :: String}
  deriving (Eq, Ord, Read, Show)

_Url = (Core.Name "org/stacspec/items.Url")
