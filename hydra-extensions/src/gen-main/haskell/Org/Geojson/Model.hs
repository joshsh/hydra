-- | A GeoJSON model based on the specification at https://www.rfc-editor.org/rfc/rfc7946. This model provides some additional structure beyond the JSON encoding described in the specification; For example, it provides MultiPoint not as an object with an array of coordinates which encode points, but as an array of Points. A BoundingBox is not simply an list of numbers, but a list of CoordinateRanges.

module Org.Geojson.Model where

import qualified Hydra.Core as Core
import qualified Hydra.Json as Model
import Data.List
import Data.Map
import Data.Set

-- | A GeoJSON object MAY have a member named "bbox" to include information on the coordinate range for its Geometries, Features, or FeatureCollections.  The value of the bbox member MUST be an array of length 2*n where n is the number of dimensions represented in the contained geometries, with all axes of the most southwesterly point followed by all axes of the more northeasterly point.  The axes order of a bbox follows the axes order of geometries.
newtype BoundingBox = 
  BoundingBox {
    -- | A GeoJSON object MAY have a member named "bbox" to include information on the coordinate range for its Geometries, Features, or FeatureCollections.  The value of the bbox member MUST be an array of length 2*n where n is the number of dimensions represented in the contained geometries, with all axes of the most southwesterly point followed by all axes of the more northeasterly point.  The axes order of a bbox follows the axes order of geometries.
    unBoundingBox :: [CoordinateRange]}
  deriving (Eq, Ord, Read, Show)

_BoundingBox = (Core.Name "org/geojson/model.BoundingBox")

data CoordinateRange = 
  CoordinateRange {
    coordinateRangeMin :: Double,
    coordinateRangeMax :: Double}
  deriving (Eq, Ord, Read, Show)

_CoordinateRange = (Core.Name "org/geojson/model.CoordinateRange")

_CoordinateRange_min = (Core.Name "min")

_CoordinateRange_max = (Core.Name "max")

-- | A Feature object represents a spatially bounded thing.  Every Feature object is a GeoJSON object no matter where it occurs in a GeoJSON text.
data Feature = 
  Feature {
    -- | A Feature object has a member with the name "geometry".  The value of the geometry member SHALL be either a Geometry object as defined above or, in the case that the Feature is unlocated, a JSON null value.
    featureGeometry :: (Maybe Geometry),
    -- | A Feature object has a member with the name "properties".  The value of the properties member is an object (any JSON object or a JSON null value).
    featureProperties :: (Maybe (Map String Model.Value)),
    -- | If a Feature has a commonly used identifier, that identifier SHOULD be included as a member of the Feature object with the name "id", and the value of this member is either a JSON string or number.
    featureId :: (Maybe Id),
    featureBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_Feature = (Core.Name "org/geojson/model.Feature")

_Feature_geometry = (Core.Name "geometry")

_Feature_properties = (Core.Name "properties")

_Feature_id = (Core.Name "id")

_Feature_bbox = (Core.Name "bbox")

-- | A GeoJSON object with the type "FeatureCollection" is a FeatureCollection object.  A FeatureCollection object has a member with the name "features".  The value of "features" is a JSON array. Each element of the array is a Feature object as defined above.  It is possible for this array to be empty.
data FeatureCollection = 
  FeatureCollection {
    featureCollectionFeatures :: [Feature],
    featureCollectionBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_FeatureCollection = (Core.Name "org/geojson/model.FeatureCollection")

_FeatureCollection_features = (Core.Name "features")

_FeatureCollection_bbox = (Core.Name "bbox")

-- | A GeoJSON object with type "GeometryCollection" is a Geometry object. A GeometryCollection has a member with the name "geometries".  The value of "geometries" is an array.  Each element of this array is a GeoJSON Geometry object.  It is possible for this array to be empty.
data GeometryCollection = 
  GeometryCollection {
    geometryCollectionGeometries :: [Geometry],
    geometryCollectionBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_GeometryCollection = (Core.Name "org/geojson/model.GeometryCollection")

_GeometryCollection_geometries = (Core.Name "geometries")

_GeometryCollection_bbox = (Core.Name "bbox")

-- | A Geometry object represents points, curves, and surfaces in coordinate space.  Every Geometry object is a GeoJSON object no matter where it occurs in a GeoJSON text.
data Geometry = 
  GeometryPoint Point |
  GeometryMultiPoint MultiPoint |
  GeometryLineString LineString |
  GeometryMultiLineString MultiLineString |
  GeometryPolygon Polygon |
  GeometryMultiPolygon MultiPolygon |
  GeometryGeometryCollection GeometryCollection
  deriving (Eq, Ord, Read, Show)

_Geometry = (Core.Name "org/geojson/model.Geometry")

_Geometry_point = (Core.Name "point")

_Geometry_multiPoint = (Core.Name "multiPoint")

_Geometry_lineString = (Core.Name "lineString")

_Geometry_multiLineString = (Core.Name "multiLineString")

_Geometry_polygon = (Core.Name "polygon")

_Geometry_multiPolygon = (Core.Name "multiPolygon")

_Geometry_geometryCollection = (Core.Name "geometryCollection")

data Id = 
  IdNumber Double |
  IdString String
  deriving (Eq, Ord, Read, Show)

_Id = (Core.Name "org/geojson/model.Id")

_Id_number = (Core.Name "number")

_Id_string = (Core.Name "string")

-- | For type "LineString", the "coordinates" member is an array of two or more positions.
data LineString = 
  LineString {
    lineStringCoordinates :: [Position],
    lineStringBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_LineString = (Core.Name "org/geojson/model.LineString")

_LineString_coordinates = (Core.Name "coordinates")

_LineString_bbox = (Core.Name "bbox")

-- | For type "MultiLineString", the "coordinates" member is an array of LineString coordinate arrays.
data MultiLineString = 
  MultiLineString {
    multiLineStringCoordinates :: [LineString],
    multiLineStringBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_MultiLineString = (Core.Name "org/geojson/model.MultiLineString")

_MultiLineString_coordinates = (Core.Name "coordinates")

_MultiLineString_bbox = (Core.Name "bbox")

-- | For type "MultiPoint", the "coordinates" member is an array of positions.
data MultiPoint = 
  MultiPoint {
    multiPointCoordinates :: [Point],
    multiPointBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_MultiPoint = (Core.Name "org/geojson/model.MultiPoint")

_MultiPoint_coordinates = (Core.Name "coordinates")

_MultiPoint_bbox = (Core.Name "bbox")

-- | For type "MultiPolygon", the "coordinates" member is an array of Polygon coordinate arrays.
data MultiPolygon = 
  MultiPolygon {
    multiPolygonCoordinates :: [Polygon],
    multiPolygonBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_MultiPolygon = (Core.Name "org/geojson/model.MultiPolygon")

_MultiPolygon_coordinates = (Core.Name "coordinates")

_MultiPolygon_bbox = (Core.Name "bbox")

-- | A GeoJSON object represents a Geometry, Feature, or collection of Features.
data Object = 
  ObjectGeometry Geometry |
  ObjectFeature Feature |
  ObjectFeatureCollection FeatureCollection
  deriving (Eq, Ord, Read, Show)

_Object = (Core.Name "org/geojson/model.Object")

_Object_geometry = (Core.Name "geometry")

_Object_feature = (Core.Name "feature")

_Object_featureCollection = (Core.Name "featureCollection")

-- | For type "Point", the "coordinates" member is a single position.
data Point = 
  Point {
    pointCoordinates :: Position,
    pointBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_Point = (Core.Name "org/geojson/model.Point")

_Point_coordinates = (Core.Name "coordinates")

_Point_bbox = (Core.Name "bbox")

-- | For type "Polygon", the "coordinates" member MUST be an array of linear ring coordinate arrays.
-- | For Polygons with more than one of these rings, the first MUST be the exterior ring, and any others MUST be interior rings.  The exterior ring bounds the surface, and the interior rings (if present) bound holes within the surface.
data Polygon = 
  Polygon {
    polygonCoordinates :: [Position],
    polygonBbox :: (Maybe BoundingBox)}
  deriving (Eq, Ord, Read, Show)

_Polygon = (Core.Name "org/geojson/model.Polygon")

_Polygon_coordinates = (Core.Name "coordinates")

_Polygon_bbox = (Core.Name "bbox")

-- | A position is an array of numbers.  There MUST be two or more elements.  The first two elements are longitude and latitude, or easting and northing, precisely in that order and using decimal numbers.  Altitude or elevation MAY be included as an optional third element.
data Position = 
  Position {
    positionLatitude :: Double,
    positionLongitude :: Double,
    positionAltitude :: (Maybe Double)}
  deriving (Eq, Ord, Read, Show)

_Position = (Core.Name "org/geojson/model.Position")

_Position_latitude = (Core.Name "latitude")

_Position_longitude = (Core.Name "longitude")

_Position_altitude = (Core.Name "altitude")
