package hydra.ext.json;

import hydra.json.Value;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

public class JsonCodingTest {
    @Test
    public void testObjectOrderingIsPreserved() {
        Value v = new JsonEncoding.ObjectBuilder()
                .put("q", JsonEncoding.toJson(1))
                .put("zz", JsonEncoding.toJson(2))
                .put("aaa", JsonEncoding.toJson(3))
                .put("f", JsonEncoding.toJson(5))
                .put("55", JsonEncoding.toJson(6))
                .build();
        v.accept(new Value.PartialVisitor<String>() {
            @Override
            public String otherwise(Value instance) {
                fail("expected an object");
                return null;
            }

            @Override
            public String visit(Value.Object_ instance) {
                StringBuilder sb = new StringBuilder();
                for (Map.Entry<String, Value> e : instance.value.entrySet()) {
                    sb.append(e.getKey());
                }
                assertEquals("qzzaaaf55", sb.toString());
                return null;
            }
        });
    }

    @Test
    public void testSetOrderingIsPreserved() {
        Set<String> decoded = JsonDecoding.decodeSet(value -> value.accept(new Value.PartialVisitor<String>() {
            @Override
            public String otherwise(Value instance) {
                fail("unexpected value");
                return null;
            }

            @Override
            public String visit(Value.String_ instance) {
                return instance.value;
            }
        }), JsonEncoding.toJson(Arrays.asList("b", "x", "yy", "123", "aaaa", "w")));
        StringBuilder sb = new StringBuilder();
        for (String s : decoded) {
            sb.append(s);
        }
        assertEquals("bxyy123aaaaw", sb.toString());
    }
}
