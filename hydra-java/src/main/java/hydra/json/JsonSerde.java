package hydra.ext.json;

import com.cedarsoftware.util.io.JsonReader;
import com.cedarsoftware.util.io.JsonWriter;
import hydra.dsl.Flows;
import hydra.compute.Coder;
import hydra.compute.Flow;
import hydra.json.Value;

import java.util.HashMap;
import java.util.Map;

/**
 * A bidirectional coder between Hydra's native JSON values and strings (via json-io).
 */
public class JsonSerde<S1, S2> extends Coder<S1, S2, Value, String> {
    private static final Map<String, Object> WRITER_ARGS = new HashMap<String, Object>() {{
        put(JsonWriter.TYPE, false);
        put(JsonWriter.PRETTY_PRINT, false);
        //put(JsonWriter.SKIP_NULL_FIELDS, true);
    }};

    public JsonSerde() {
        super(JsonSerde::encode, JsonSerde::decode);
    }

    /**
     * Encode a JSON value to a string.
     */
    public static <S> Flow<S, String> encode(Value value) {
        return Flows.map(JsonIoCoder.encode(value),
                raw -> JsonWriter.objectToJson(JsonIoCoder.normalizeEncoded(raw), WRITER_ARGS));
    }

    /**
     * Decode a JSON value from a string.
     */
    public static <S> Flow<S, Value> decode(String value) {
        Object json;
        try {
            json = JsonReader.jsonToJava(value);
        } catch (Exception e) {
            return Flows.fail("JSON parse error", e);
        }

        return JsonIoCoder.decode(json);
    }
}
