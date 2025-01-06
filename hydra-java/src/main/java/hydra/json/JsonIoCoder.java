package hydra.ext.json;

import com.cedarsoftware.util.io.JsonObject;
import hydra.dsl.Flows;
import hydra.compute.Coder;
import hydra.compute.Flow;
import hydra.json.Value;

import java.util.Collection;
import java.util.List;
import java.util.Map;

/**
 * A bidirectional coder between Hydra's native JSON values and the JSON objects supported by json-io.
 */
public class JsonIoCoder<S1, S2> extends Coder<S1, S2, Value, Object> {
    public JsonIoCoder() {
        super(JsonIoCoder::encode, JsonIoCoder::decode);
    }

    /**
     * Encode a JSON value as a json-io object.
     */
    public static <S> Flow<S, Object> encode(Value value) {
        return value.accept(new Value.Visitor<Flow<S, Object>>() {
            @Override
            public Flow<S, Object> visit(Value.Array instance) {
                return Flows.map(Flows.mapM(instance.value, JsonIoCoder::encode), List::toArray);
            }

            @Override
            public Flow<S, Object> visit(Value.Boolean_ instance) {
                return Flows.pure(instance.value);
            }

            @Override
            public Flow<S, Object> visit(Value.Null instance) {
                // Note: we return an object here rather than a null, as Hydra flows cannot accept nulls as values.
                //       This is acceptable so long as we are only using the generated java-io objects internally,
                //       for serialization. See normalizeEncoded().
                return Flows.pure(instance);
            }

            @Override
            public Flow<S, Object> visit(Value.Number_ instance) {
                return Flows.pure(instance.value);
            }

            @Override
            public Flow<S, Object> visit(Value.Object_ instance) {
                return Flows.map(Flows.mapM(instance.value, Flows::pure, JsonIoCoder::encode), m -> {
                    JsonObject obj = new JsonObject();
                    obj.putAll(m);
                    return obj;
                });
            }

            @Override
            public Flow<S, Object> visit(Value.String_ instance) {
                return Flows.pure(instance.value);
            }
        });
    }

    /**
     * Decode a json-io object as a JSON value.
     */
    public static <S> Flow<S, Value> decode(Object value) {
        if (value == null) {
            return Flows.pure(new Value.Null());
        } else if (value.getClass().isArray()) {
            Object[] array = (Object[]) value;
            return Flows.map(Flows.mapM(array, JsonIoCoder::decode), Value.Array::new);
        } else if (value instanceof JsonObject) {
            return Flows.map(Flows.mapM((Map<Object, Object>) value, JsonIoCoder::decodeKey, JsonIoCoder::decode),
                    Value.Object_::new);
        } else if (value instanceof String) {
            return Flows.pure(new Value.String_((String) value));
        } else if (value instanceof Boolean) {
            return Flows.pure(new Value.Boolean_((Boolean) value));
        } else if (value instanceof Number) {
            return Flows.pure(new Value.Number_(((Number) value).doubleValue()));
        } else {
            return Flows.unexpected("object, array, string, boolean, or number", value.getClass().getName());
        }
    }

    /**
     * Normalize an already-encoded json-io object.
     */
    public static Object normalizeEncoded(Object raw) {
        if (raw instanceof Value.Null) {
            return null;
        } else if (raw.getClass().isArray()) {
            Object[] rawArray = (Object[]) raw;
            Object[] normed = new Object[rawArray.length];
            for (int i = 0; i < rawArray.length; i++) {
                normed[i] = normalizeEncoded(rawArray[i]);
            }
            return normed;
        } else if (raw instanceof JsonObject) {
            JsonObject rawObj = (JsonObject) raw;
            JsonObject normed = new JsonObject();
            Collection<Map.Entry<Object, Object>> entries = rawObj.entrySet();
            for (Map.Entry<Object, Object> entry : entries) {
                normed.put(entry.getKey(), normalizeEncoded(entry.getValue()));
            }
            return normed;
        } else {
            return raw;
        }
    }

    private static <S> Flow<S, String> decodeKey(Object key) {
        if (key instanceof String) {
            return Flows.pure((String) key);
        } else {
            return Flows.unexpected("string", key.getClass().getName());
        }
    }
}
