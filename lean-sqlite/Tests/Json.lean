import LSql.Json

/-! Tests for LSql.Json. Every expected value was produced by the real sqlite3 3.54.0 (the SQL expression is in the
comment above each check; control characters in a result were compared as hex). A test expression is built with T.c "FUNC" #[args]; a nested JSON function result is
marked as JSON (sqlite's subtype), as in sqlite. -/

open LSql LSql.Json

namespace TJ

/-- A SQL value, or an error, with the flag "this came from a JSON function". -/
abbrev T := Except String (Value × Bool)

def T.n : T := .ok (.null, false)
def T.t (s : String) : T := .ok (.text s, false)
def T.i (i : Int64) : T := .ok (.int i, false)
def T.r (f : Float) : T := .ok (.real f, false)

def hexByte (c : UInt8) : UInt8 := if c >= 97 then c - 87 else if c >= 65 then c - 55 else c - 48

def T.b (hex : String) : T :=
  let b := hex.toUTF8
  .ok (.blob (ByteArray.mk ((List.range (b.size / 2)).toArray.map fun k => hexByte (bAt b (2 * k)) * 16 + hexByte (bAt b (2 * k + 1)))), false)

def T.c (name : String) (as : Array T) : T := do
  let vs ← as.mapM id
  callJ name (vs.map (·.1)) (vs.map (·.2))

def show' : T → String
  | .error e => "E:" ++ e
  | .ok (.null, _) => "null:"
  | .ok (.int i, _) => "integer:" ++ Num.int64ToText i
  | .ok (.real f, _) => "real:" ++ Num.fmtReal f
  | .ok (.text s, _) => "text:" ++ s
  | .ok (.blob _, _) => "blob:"

def rowsText (r : Except String (Array (Array Value))) : String :=
  match r with
  | .error e => "E:" ++ e
  | .ok rows => "\n".intercalate (rows.toList.map fun row => "|".intercalate (row.toList.map Value.toText))

def agg (name : String) (rows : Array (Array T)) : String :=
  let step (acc : Agg) (row : Array T) : Agg :=
    match row.mapM id with
    | .error e => { acc with err := some e }
    | .ok vs => aggStep name acc (vs.map (·.1)) (vs.map (·.2))
  show' ((aggFinal name (rows.foldl step {})).map fun v => (v, true))


def T.v (t : T) : Value := match t with | .ok (v, _) => v | .error _ => .null

end TJ
open TJ

/-! Scalar functions -/

-- select json('{"a" : [1, 2 ,3] , "b":{"c":null}}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\" : [1, 2 ,3] , \"b\":{\"c\":null}}"]) == "text:{\"a\":[1,2,3],\"b\":{\"c\":null}}"
-- select json(' [ ] ');
#guard TJ.show' (T.c "JSON" #[T.t " [ ] "]) == "text:[]"
-- select json('{}');
#guard TJ.show' (T.c "JSON" #[T.t "{}"]) == "text:{}"
-- select json('true');
#guard TJ.show' (T.c "JSON" #[T.t "true"]) == "text:true"
-- select json('"a\nb"');
#guard TJ.show' (T.c "JSON" #[T.t "\"a\\nb\""]) == "text:\"a\\nb\""
-- select json('1.50');
#guard TJ.show' (T.c "JSON" #[T.t "1.50"]) == "text:1.50"
-- select json('-0');
#guard TJ.show' (T.c "JSON" #[T.t "-0"]) == "text:-0"
-- select json('1e5');
#guard TJ.show' (T.c "JSON" #[T.t "1e5"]) == "text:1e5"
-- select json('123456789012345678901234567890');
#guard TJ.show' (T.c "JSON" #[T.t "123456789012345678901234567890"]) == "text:123456789012345678901234567890"
-- select json('[1,2,]');
#guard TJ.show' (T.c "JSON" #[T.t "[1,2,]"]) == "text:[1,2]"
-- select json('{"a":1,}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\":1,}"]) == "text:{\"a\":1}"
-- select json('[1,2');
#guard TJ.show' (T.c "JSON" #[T.t "[1,2"]) == "E:malformed JSON"
-- select json('');
#guard TJ.show' (T.c "JSON" #[T.t ""]) == "E:malformed JSON"
-- select json(NULL);
#guard TJ.show' (T.c "JSON" #[T.n]) == "null:"
-- select json(5);
#guard TJ.show' (T.c "JSON" #[T.i (5)]) == "text:5"
-- select json(1.5);
#guard TJ.show' (T.c "JSON" #[T.r (1.5)]) == "text:1.5"
-- select json('nan');
#guard TJ.show' (T.c "JSON" #[T.t "nan"]) == "text:null"
-- select json('[Infinity,-Infinity,NaN,+5,.5,5.,0x1F,-0xff,1.e2]');
#guard TJ.show' (T.c "JSON" #[T.t "[Infinity,-Infinity,NaN,+5,.5,5.,0x1F,-0xff,1.e2]"]) == "text:[9e999,-9e999,null,5,0.5,5.0,31,-255,1.0e2]"
-- select json('[+inf,-INF,infinity]');
#guard TJ.show' (T.c "JSON" #[T.t "[+inf,-INF,infinity]"]) == "text:[9e999,-9e999,9e999]"
-- select json('{"a":1}x');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\":1}x"]) == "E:malformed JSON"
-- select json('[1,2]  ');
#guard TJ.show' (T.c "JSON" #[T.t "[1,2]  "]) == "text:[1,2]"
-- select json('01');
#guard TJ.show' (T.c "JSON" #[T.t "01"]) == "E:malformed JSON"
-- select json('1.2.3');
#guard TJ.show' (T.c "JSON" #[T.t "1.2.3"]) == "E:malformed JSON"
-- select json('-');
#guard TJ.show' (T.c "JSON" #[T.t "-"]) == "E:malformed JSON"
-- select json('"abc');
#guard TJ.show' (T.c "JSON" #[T.t "\"abc"]) == "E:malformed JSON"
-- select json('[1 2]');
#guard TJ.show' (T.c "JSON" #[T.t "[1 2]"]) == "E:malformed JSON"
-- select json('{"a" 1}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\" 1}"]) == "E:malformed JSON"
-- select json('{1:2}');
#guard TJ.show' (T.c "JSON" #[T.t "{1:2}"]) == "E:malformed JSON"
-- select json('{"a":}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\":}"]) == "E:malformed JSON"
-- select json('[,]');
#guard TJ.show' (T.c "JSON" #[T.t "[,]"]) == "E:malformed JSON"
-- select json('{,}');
#guard TJ.show' (T.c "JSON" #[T.t "{,}"]) == "E:malformed JSON"
-- select json('[1,,2]');
#guard TJ.show' (T.c "JSON" #[T.t "[1,,2]"]) == "E:malformed JSON"
-- select json('tru');
#guard TJ.show' (T.c "JSON" #[T.t "tru"]) == "E:malformed JSON"
-- select json('nulll');
#guard TJ.show' (T.c "JSON" #[T.t "nulll"]) == "E:malformed JSON"
-- select json('[true,false,null]');
#guard TJ.show' (T.c "JSON" #[T.t "[true,false,null]"]) == "text:[true,false,null]"
-- select json('"\u00e9\u0041"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\u00e9\\u0041\""]) == "text:\"\\u00e9\\u0041\""
-- select json('"\x41"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\x41\""]) == "text:\"\\u0041\""
-- select json('{"a\"b":1}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\\\"b\":1}"]) == "text:{\"a\\\"b\":1}"
-- select json(x'7b7d');
#guard TJ.show' (T.c "JSON" #[T.b "7b7d"]) == "text:{}"
-- select json(char(34)||char(9)||char(34));
#guard TJ.show' (T.c "JSON" #[T.t "\"\x09\""]) == "text:\"\\t\""
-- select json_quote('abc');
#guard TJ.show' (T.c "JSON_QUOTE" #[T.t "abc"]) == "text:\"abc\""
-- select json_quote('a"b\c/d''e');
#guard TJ.show' (T.c "JSON_QUOTE" #[T.t "a\"b\\c/d'e"]) == "text:\"a\\\"b\\\\c/d'e\""
-- select json_quote(char(1,2,8,9,10,12,13,31));
#guard TJ.show' (T.c "JSON_QUOTE" #[T.t "\x01\x02\x08\x09\x0a\x0c\x0d\x1f"]) == "text:\"\\u0001\\u0002\\b\\t\\n\\f\\r\\u001f\""
-- select json_quote(NULL);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.n]) == "text:null"
-- select json_quote(12);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.i (12)]) == "text:12"
-- select json_quote(1.5);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (1.5)]) == "text:1.5"
-- select json_quote(1e999);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r Num.posInf]) == "text:9.0e+999"
-- select json_quote(-1e999);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (-Num.posInf)]) == "text:-9.0e+999"
-- select json_quote(json('[1, 2]'));
#guard TJ.show' (T.c "JSON_QUOTE" #[T.c "JSON" #[T.t "[1, 2]"]]) == "text:[1,2]"
-- select json_quote('[1,2]');
#guard TJ.show' (T.c "JSON_QUOTE" #[T.t "[1,2]"]) == "text:\"[1,2]\""
-- select json_quote(x'00');
#guard TJ.show' (T.c "JSON_QUOTE" #[T.b "00"]) == "text:null"
-- select json_array();
#guard TJ.show' (T.c "JSON_ARRAY" #[]) == "text:[]"
-- select json_array(1,'a',NULL,1.5,2.0,1e20,0.1);
#guard TJ.show' (T.c "JSON_ARRAY" #[T.i (1), T.t "a", T.n, T.r (1.5), T.r (2.0), T.r (1.0e20), T.r (0.1)]) == "text:[1,\"a\",null,1.5,2.0,1.0e+20,0.1]"
-- select json_array(json('[1, 2]'),'[3, 4]');
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON" #[T.t "[1, 2]"], T.t "[3, 4]"]) == "text:[[1,2],\"[3, 4]\"]"
-- select json_array(1e999,-1e999);
#guard TJ.show' (T.c "JSON_ARRAY" #[T.r Num.posInf, T.r (-Num.posInf)]) == "text:[9.0e+999,-9.0e+999]"
-- select json_array(x'01');
#guard TJ.show' (T.c "JSON_ARRAY" #[T.b "01"]) == "text:[true]"
-- select json_array(-0.0);
#guard TJ.show' (T.c "JSON_ARRAY" #[T.r (-0.0)]) == "text:[0.0]"
-- select json_array(123456789012345.0,1e15,1.5e300);
#guard TJ.show' (T.c "JSON_ARRAY" #[T.r (123456789012345.0), T.r (1.0e15), T.r (1.5e300)]) == "text:[123456789012345.0,1000000000000000.0,1.5e+300]"
-- select json_object();
#guard TJ.show' (T.c "JSON_OBJECT" #[]) == "text:{}"
-- select json_object('a',1,'b','x','c',NULL);
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "a", T.i (1), T.t "b", T.t "x", T.t "c", T.n]) == "text:{\"a\":1,\"b\":\"x\",\"c\":null}"
-- select json_object('a',json('{"x": 1}'));
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "a", T.c "JSON" #[T.t "{\"x\": 1}"]]) == "text:{\"a\":{\"x\":1}}"
-- select json_object('a');
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "a"]) == "E:json_object() requires an even number of arguments"
-- select json_object(1,2);
#guard TJ.show' (T.c "JSON_OBJECT" #[T.i (1), T.i (2)]) == "E:json_object() labels must be TEXT"
-- select json_object(NULL,1);
#guard TJ.show' (T.c "JSON_OBJECT" #[T.n, T.i (1)]) == "E:json_object() labels must be TEXT"
-- select json_object('k"',2,'é',3);
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "k\"", T.i (2), T.t "é", T.i (3)]) == "text:{\"k\\\"\":2,\"é\":3}"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.a"]) == "integer:1"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.b');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.b"]) == "text:[1,2,{\"c\":\"x\"}]"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.b[2].c');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.b[2].c"]) == "text:x"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.b[#-1].c');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.b[#-1].c"]) == "text:x"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.b[#-3]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.b[#-3]"]) == "integer:1"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.b[#-4]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.b[#-4]"]) == "null:"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.b[#]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.b[#]"]) == "null:"
-- select json_extract('{"a":1,"b":[1,2,{"c":"x"}]}','$.z');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"b\":[1,2,{\"c\":\"x\"}]}", T.t "$.z"]) == "null:"
-- select json_extract('{"a":1}','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t "$"]) == "text:{\"a\":1}"
-- select json_extract('[1,2]','$[0]','$[1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2]", T.t "$[0]", T.t "$[1]"]) == "text:[1,2]"
-- select json_extract('[1,2]','$[0]','$[5]','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2]", T.t "$[0]", T.t "$[5]", T.t "$"]) == "text:[1,null,[1,2]]"
-- select json_extract('{"a":1}','$.a','$.b');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t "$.a", T.t "$.b"]) == "text:[1,null]"
-- select json_extract('{"a":1}','a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t "a"]) == "E:bad JSON path: 'a'"
-- select json_extract('{"a":1}','$.a.');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t "$.a."]) == "E:bad JSON path: '$.a.'"
-- select json_extract('{"a":1}','$..a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t "$..a"]) == "E:bad JSON path: '$..a'"
-- select json_extract('{"a":1}','$.');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t "$."]) == "E:bad JSON path: '$.'"
-- select json_extract('{"a b":2}','$."a b"');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a b\":2}", T.t "$.\"a b\""]) == "integer:2"
-- select json_extract('{"a b":2}','$."a b');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a b\":2}", T.t "$.\"a b"]) == "E:bad JSON path: '$.\"a b'"
-- select json_extract('{"a.b":2}','$."a.b"');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a.b\":2}", T.t "$.\"a.b\""]) == "integer:2"
-- select json_extract('{"a\"b":2}','$."a\"b"');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\\\"b\":2}", T.t "$.\"a\\\"b\""]) == "integer:2"
-- select json_extract('{"a":{"b":[10,20]}}','$.a.b[1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":{\"b\":[10,20]}}", T.t "$.a.b[1]"]) == "integer:20"
-- select json_extract('{"a":{"b":[10,20]}}','$.a.b[x]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":{\"b\":[10,20]}}", T.t "$.a.b[x]"]) == "E:bad JSON path: '$.a.b[x]'"
-- select json_extract('{"a":{"b":[10,20]}}','$.a.b[1');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":{\"b\":[10,20]}}", T.t "$.a.b[1"]) == "E:bad JSON path: '$.a.b[1'"
-- select json_extract('{"a":{"b":[10,20]}}','$.x[');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":{\"b\":[10,20]}}", T.t "$.x["]) == "null:"
-- select json_extract('{"a":{"b":[10,20]}}','$.a[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":{\"b\":[10,20]}}", T.t "$.a[0]"]) == "null:"
-- select json_extract('[1,2,3]','$[#-1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2,3]", T.t "$[#-1]"]) == "integer:3"
-- select json_extract('[1,2,3]','$[#-0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2,3]", T.t "$[#-0]"]) == "null:"
-- select json_extract('[1,2,3]','$[#--1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2,3]", T.t "$[#--1]"]) == "E:bad JSON path: '$[#--1]'"
-- select json_extract('[1,2,3]','$[ 1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2,3]", T.t "$[ 1]"]) == "E:bad JSON path: '$[ 1]'"
-- select json_extract('[1,2,3]','$[99999999999]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2,3]", T.t "$[99999999999]"]) == "null:"
-- select json_extract('[1,2,3]','$[1]x');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2,3]", T.t "$[1]x"]) == "E:bad JSON path: '$[1]x'"
-- select json_extract('{"a":"he said \"hi\"\n\u00e9"}','$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":\"he said \\\"hi\\\"\\n\\u00e9\"}", T.t "$.a"]) == "text:he said \"hi\"\x0aé"
-- select json_extract('{"a":true,"b":false,"c":null}','$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":true,\"b\":false,\"c\":null}", T.t "$.a"]) == "integer:1"
-- select json_extract('{"a":true,"b":false,"c":null}','$.b');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":true,\"b\":false,\"c\":null}", T.t "$.b"]) == "integer:0"
-- select json_extract('{"a":true,"b":false,"c":null}','$.c');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":true,\"b\":false,\"c\":null}", T.t "$.c"]) == "null:"
-- select json_extract('{"a":true,"b":false,"c":null}','$.a','$.b','$.c');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":true,\"b\":false,\"c\":null}", T.t "$.a", T.t "$.b", T.t "$.c"]) == "text:[true,false,null]"
-- select json_extract('1.0','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "1.0", T.t "$"]) == "real:1.0"
-- select json_extract('1e2','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "1e2", T.t "$"]) == "real:100.0"
-- select json_extract('9223372036854775807','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "9223372036854775807", T.t "$"]) == "integer:9223372036854775807"
-- select json_extract('9223372036854775808','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "9223372036854775808", T.t "$"]) == "real:9.2233720368547758e+18"
-- select json_extract('-9223372036854775808','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "-9223372036854775808", T.t "$"]) == "integer:-9223372036854775808"
-- select json_extract('123456789012345678901','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "123456789012345678901", T.t "$"]) == "real:1.2345678901234568e+20"
-- select json_extract('0.1','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "0.1", T.t "$"]) == "real:0.1"
-- select json_extract('"x"','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "\"x\"", T.t "$"]) == "text:x"
-- select json_extract('[1.0,2.50]','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1.0,2.50]", T.t "$"]) == "text:[1.0,2.50]"
-- select json_extract('[1,2]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2]"]) == "null:"
-- select json_extract(NULL,'$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.n, T.t "$"]) == "null:"
-- select json_extract('{}',NULL);
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{}", T.n]) == "null:"
-- select json_extract('{bad','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{bad", T.t "$"]) == "E:malformed JSON"
-- select json_extract('[0x10]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[0x10]", T.t "$[0]"]) == "integer:16"
-- select json_extract('[Infinity]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[Infinity]", T.t "$[0]"]) == "real:Inf"
-- select json_extract('[NaN]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[NaN]", T.t "$[0]"]) == "null:"
-- select json_extract('{"a":1,"a":2}','$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1,\"a\":2}", T.t "$.a"]) == "integer:1"
-- select json_extract('{"":5}','$.""');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"\":5}", T.t "$.\"\""]) == "integer:5"
-- select json_extract('{"a":[]}','$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":[]}", T.t "$.a"]) == "text:[]"
-- select json_extract('{"a":{}}','$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":{}}", T.t "$.a"]) == "text:{}"
-- select '{"a":[1,2]}' -> '$.a';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":[1,2]}", T.t "$.a"]) == "text:[1,2]"
-- select '{"a":[1,2]}' -> 'a';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":[1,2]}", T.t "a"]) == "text:[1,2]"
-- select '{"a":[1,2]}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":[1,2]}", T.t "a"]) == "text:[1,2]"
-- select '{"a":[1,2]}' -> 'a' ->> 1;
#guard TJ.show' (T.c "->>" #[T.c "->" #[T.t "{\"a\":[1,2]}", T.t "a"], T.i (1)]) == "integer:2"
-- select '[1,2,3]' ->> -1;
#guard TJ.show' (T.c "->>" #[T.t "[1,2,3]", T.i (-1)]) == "integer:3"
-- select '[1,2,3]' -> 0;
#guard TJ.show' (T.c "->" #[T.t "[1,2,3]", T.i (0)]) == "text:1"
-- select '[1,2,3]' -> 5;
#guard TJ.show' (T.c "->" #[T.t "[1,2,3]", T.i (5)]) == "null:"
-- select '[1,2,3]' -> '[1]';
#guard TJ.show' (T.c "->" #[T.t "[1,2,3]", T.t "[1]"]) == "text:2"
-- select '{"a":"x"}' -> 'a';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":\"x\"}", T.t "a"]) == "text:\"x\""
-- select '{"a":"x"}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":\"x\"}", T.t "a"]) == "text:x"
-- select '{"a b":"x"}' ->> 'a b';
#guard TJ.show' (T.c "->>" #[T.t "{\"a b\":\"x\"}", T.t "a b"]) == "text:x"
-- select '{"a":null}' -> 'a';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":null}", T.t "a"]) == "text:null"
-- select '{"a":null}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":null}", T.t "a"]) == "null:"
-- select '{"a":1.5}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":1.5}", T.t "a"]) == "real:1.5"
-- select '{"a":true}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":true}", T.t "a"]) == "integer:1"
-- select '{"a":true}' -> 'a';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":true}", T.t "a"]) == "text:true"
-- select '[1]' -> 1.5;
#guard TJ.show' (T.c "->" #[T.t "[1]", T.r (1.5)]) == "null:"
-- select '{"a":1}' ->> '$.a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":1}", T.t "$.a"]) == "integer:1"
-- select '{"a":1}' -> '';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":1}", T.t ""]) == "E:bad JSON path: ''"
-- select 'bad' -> 'a';
#guard TJ.show' (T.c "->" #[T.t "bad", T.t "a"]) == "E:malformed JSON"
-- select '[1,2,3]' -> '[#-1]';
#guard TJ.show' (T.c "->" #[T.t "[1,2,3]", T.t "[#-1]"]) == "text:3"
-- select '[[1,2],[3]]' -> 0 -> 1;
#guard TJ.show' (T.c "->" #[T.c "->" #[T.t "[[1,2],[3]]", T.i (0)], T.i (1)]) == "text:2"
-- select NULL -> 'a';
#guard TJ.show' (T.c "->" #[T.n, T.t "a"]) == "null:"
-- select '{"a":1}' -> NULL;
#guard TJ.show' (T.c "->" #[T.t "{\"a\":1}", T.n]) == "null:"
-- select '{"a":1}' ->> 'b';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":1}", T.t "b"]) == "null:"
-- select '{"a_b":1}' ->> 'a_b';
#guard TJ.show' (T.c "->>" #[T.t "{\"a_b\":1}", T.t "a_b"]) == "integer:1"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}"]) == "text:object"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a"]) == "text:array"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a[0]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a[0]"]) == "text:integer"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a[1]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a[1]"]) == "text:real"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a[2]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a[2]"]) == "text:text"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a[3]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a[3]"]) == "text:null"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a[4]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a[4]"]) == "text:true"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a[5]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a[5]"]) == "text:false"
-- select json_type('{"a":[1,2.5,"x",null,true,false,{}]}','$.a[6]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":[1,2.5,\"x\",null,true,false,{}]}", T.t "$.a[6]"]) == "text:object"
-- select json_type('{"a":1}','$.b');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":1}", T.t "$.b"]) == "null:"
-- select json_type('{"a":1}','b');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "{\"a\":1}", T.t "b"]) == "E:bad JSON path: 'b'"
-- select json_type('x');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "x"]) == "E:malformed JSON"
-- select json_type(NULL);
#guard TJ.show' (T.c "JSON_TYPE" #[T.n]) == "null:"
-- select json_type(5);
#guard TJ.show' (T.c "JSON_TYPE" #[T.i (5)]) == "text:integer"
-- select json_type('12345678901234567890');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "12345678901234567890"]) == "text:integer"
-- select json_type('[]','$[0]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "[]", T.t "$[0]"]) == "null:"
-- select json_valid('{"a":1}');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{\"a\":1}"]) == "integer:1"
-- select json_valid('{a:1}');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{a:1}"]) == "integer:0"
-- select json_valid('{a:1}',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{a:1}", T.i (2)]) == "integer:1"
-- select json_valid('[1,]');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[1,]"]) == "integer:0"
-- select json_valid('[1,]',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[1,]", T.i (2)]) == "integer:1"
-- select json_valid('');
#guard TJ.show' (T.c "JSON_VALID" #[T.t ""]) == "integer:0"
-- select json_valid(NULL);
#guard TJ.show' (T.c "JSON_VALID" #[T.n]) == "null:"
-- select json_valid(1);
#guard TJ.show' (T.c "JSON_VALID" #[T.i (1)]) == "integer:1"
-- select json_valid('1.5');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "1.5"]) == "integer:1"
-- select json_valid('abc');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "abc"]) == "integer:0"
-- select json_valid('{}',0);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{}", T.i (0)]) == "E:FLAGS parameter to json_valid() must be between 1 and 15"
-- select json_valid('{}',16);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{}", T.i (16)]) == "E:FLAGS parameter to json_valid() must be between 1 and 15"
-- select json_valid('{}',3);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{}", T.i (3)]) == "integer:1"
-- select json_valid('{}',8);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{}", T.i (8)]) == "integer:0"
-- select json_valid('{}',4);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{}", T.i (4)]) == "integer:0"
-- select json_valid('[1,2',6);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[1,2", T.i (6)]) == "integer:0"
-- select json_valid('0x10');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "0x10"]) == "integer:0"
-- select json_valid('0x10',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "0x10", T.i (2)]) == "integer:1"
-- select json_valid('[.5]');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[.5]"]) == "integer:0"
-- select json_valid('[.5]',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[.5]", T.i (2)]) == "integer:1"
-- select json_valid(' [1] ');
#guard TJ.show' (T.c "JSON_VALID" #[T.t " [1] "]) == "integer:1"
-- select json_valid('"a'||char(9)||'b"');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "\"a\x09b\""]) == "integer:0"
-- select json_valid('"a'||char(9)||'b"',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "\"a\x09b\"", T.i (2)]) == "integer:1"
-- select json_valid('[NaN]');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[NaN]"]) == "integer:0"
-- select json_valid('[1,2] x');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[1,2] x"]) == "integer:0"
-- select json_array_length('[1,2,3]');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,2,3]"]) == "integer:3"
-- select json_array_length('{}');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "{}"]) == "integer:0"
-- select json_array_length('[]');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[]"]) == "integer:0"
-- select json_array_length('[1,[2,3]]','$[1]');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,[2,3]]", T.t "$[1]"]) == "integer:2"
-- select json_array_length('[1,[2,3]]','$[0]');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,[2,3]]", T.t "$[0]"]) == "integer:0"
-- select json_array_length('[1,[2,3]]','$[5]');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,[2,3]]", T.t "$[5]"]) == "null:"
-- select json_array_length('[1,[2,3]]','x');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,[2,3]]", T.t "x"]) == "E:bad JSON path: 'x'"
-- select json_array_length('{"a":[1,2]}','$.a');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "{\"a\":[1,2]}", T.t "$.a"]) == "integer:2"
-- select json_array_length(NULL);
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.n]) == "null:"
-- select json_array_length('bad');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "bad"]) == "E:malformed JSON"
-- select json_array_length('[1]',NULL);
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1]", T.n]) == "null:"
-- select json_array_length(5);
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.i (5)]) == "integer:0"
-- select json_array_length('[1,2]','$[');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,2]", T.t "$["]) == "E:bad JSON path: '$['"
-- select json_array_length('[1,2]','$.');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,2]", T.t "$."]) == "E:bad JSON path: '$.'"
-- select json_array_length('[1,2]','$.a');
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1,2]", T.t "$.a"]) == "null:"
-- select json_error_position('[1,2]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1,2]"]) == "integer:0"
-- select json_error_position('');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t ""]) == "integer:1"
-- select json_error_position('[1,');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1,"]) == "integer:4"
-- select json_error_position('{"a" 1}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\" 1}"]) == "integer:6"
-- select json_error_position(']');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "]"]) == "integer:1"
-- select json_error_position('[1 2]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1 2]"]) == "integer:4"
-- select json_error_position('"abc');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "\"abc"]) == "integer:5"
-- select json_error_position('{"é":tru}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"é\":tru}"]) == "integer:6"
-- select json_error_position('["é",x]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[\"é\",x]"]) == "integer:6"
-- select json_error_position('{"a":1,,}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":1,,}"]) == "integer:8"
-- select json_error_position('[1,2,3');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1,2,3"]) == "integer:7"
-- select json_error_position('01');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "01"]) == "integer:2"
-- select json_error_position('[01]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[01]"]) == "integer:3"
-- select json_error_position('1.2.3');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "1.2.3"]) == "integer:4"
-- select json_error_position('[1.]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1.]"]) == "integer:0"
-- select json_error_position('[1e]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1e]"]) == "integer:3"
-- select json_error_position('[1e+]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1e+]"]) == "integer:4"
-- select json_error_position('[-]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[-]"]) == "integer:2"
-- select json_error_position('[-a]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[-a]"]) == "integer:2"
-- select json_error_position('{"a":1');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":1"]) == "integer:7"
-- select json_error_position('{"a"');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\""]) == "integer:5"
-- select json_error_position('{"a":');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":"]) == "integer:6"
-- select json_error_position('{');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{"]) == "integer:2"
-- select json_error_position('[');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "["]) == "integer:2"
-- select json_error_position('x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "x"]) == "integer:1"
-- select json_error_position('{x:1}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{x:1}"]) == "integer:0"
-- select json_error_position('{"a":1} }');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":1} }"]) == "integer:1"
-- select json_error_position('   [1 2]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "   [1 2]"]) == "integer:7"
-- select json_error_position('[1, 2  3]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1, 2  3]"]) == "integer:8"
-- select json_error_position('["a\qb"]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[\"a\\qb\"]"]) == "integer:5"
-- select json_error_position('{"a":1 "b":2}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":1 \"b\":2}"]) == "integer:8"
-- select json_error_position('{"a":[1,2}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":[1,2}"]) == "integer:10"
-- select json_error_position(NULL);
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.n]) == "null:"
-- select json_error_position(12);
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.i (12)]) == "integer:0"
-- select json_error_position('[1,2]]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1,2]]"]) == "integer:1"
-- select json_error_position(':');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t ":"]) == "integer:1"
-- select json_error_position(',');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t ","]) == "integer:1"
-- select json_error_position('[1:2]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1:2]"]) == "integer:3"
-- select json_error_position('{"a":1:2}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":1:2}"]) == "integer:7"
-- select json_error_position('{"a",1}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\",1}"]) == "integer:5"
-- select json_error_position('{ 1:2}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{ 1:2}"]) == "integer:2"
-- select json_set('{"a":1}','$.a',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.a", T.i (2)]) == "text:{\"a\":2}"
-- select json_set('{"a":1}','$.b',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.b", T.i (2)]) == "text:{\"a\":1,\"b\":2}"
-- select json_set('{"a":1}','$.b.c',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.b.c", T.i (2)]) == "text:{\"a\":1,\"b\":{\"c\":2}}"
-- select json_set('{"a":1}','$.b[0]',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.b[0]", T.i (2)]) == "text:{\"a\":1,\"b\":[2]}"
-- select json_set('{"a":1}','$.b[1]',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.b[1]", T.i (2)]) == "text:{\"a\":1}"
-- select json_set('{"a":1}','$.b[#]',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.b[#]", T.i (2)]) == "text:{\"a\":1,\"b\":[2]}"
-- select json_set('{"a":1}','$.b.c.d.e',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.b.c.d.e", T.i (2)]) == "text:{\"a\":1,\"b\":{\"c\":{\"d\":{\"e\":2}}}}"
-- select json_set('{"a":1}','$.b[0].c',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.b[0].c", T.i (2)]) == "text:{\"a\":1,\"b\":[{\"c\":2}]}"
-- select json_set('[1]','$[#]',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1]", T.t "$[#]", T.i (2)]) == "text:[1,2]"
-- select json_set('[1,2]','$[1]','x');
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1,2]", T.t "$[1]", T.t "x"]) == "text:[1,\"x\"]"
-- select json_set('[1,2]','$[2]','x');
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1,2]", T.t "$[2]", T.t "x"]) == "text:[1,2,\"x\"]"
-- select json_set('[1,2]','$[3]','x');
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1,2]", T.t "$[3]", T.t "x"]) == "text:[1,2]"
-- select json_set('[1,2]','$[#-1]','x');
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1,2]", T.t "$[#-1]", T.t "x"]) == "text:[1,\"x\"]"
-- select json_set('[1,2]','$[#-2]','x');
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1,2]", T.t "$[#-2]", T.t "x"]) == "text:[\"x\",2]"
-- select json_set('[1,2]','$[#-3]','x');
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1,2]", T.t "$[#-3]", T.t "x"]) == "text:[1,2]"
-- select json_set('{}','$','x');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$", T.t "x"]) == "text:\"x\""
-- select json_set('{}','$.a',json('{"b":1}'));
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.c "JSON" #[T.t "{\"b\":1}"]]) == "text:{\"a\":{\"b\":1}}"
-- select json_set('{}','$.a','{"b":1}');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "{\"b\":1}"]) == "text:{\"a\":\"{\\\"b\\\":1}\"}"
-- select json_set('{}','$.a',NULL);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.n]) == "text:{\"a\":null}"
-- select json_set('{}','$.a',1.5);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.r (1.5)]) == "text:{\"a\":1.5}"
-- select json_set('{}','$.a',1e999);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.r Num.posInf]) == "text:{\"a\":9e999}"
-- select json_set('{}','$."a b"',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.\"a b\"", T.i (1)]) == "text:{\"a b\":1}"
-- select json_set('{}','$."a\"b"',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.\"a\\\"b\"", T.i (1)]) == "text:{\"a\\\"b\":1}"
-- select json_set('{}','$.a"b',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a\"b", T.i (1)]) == "text:{\"a\\\"b\":1}"
-- select json_set('{}','$.a',x'00');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.b "00"]) == "text:{\"a\":null}"
-- select json_set('{}','$.a');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a"]) == "E:json_set() needs an odd number of arguments"
-- select json_set('{}',NULL,1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.n, T.i (1)]) == "text:{}"
-- select json_set('{}','a',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "a", T.i (1)]) == "E:bad JSON path: 'a'"
-- select json_set(NULL,'$.a',1);
#guard TJ.show' (T.c "JSON_SET" #[T.n, T.t "$.a", T.i (1)]) == "null:"
-- select json_set('{"a":1}');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}"]) == "text:{\"a\":1}"
-- select json_set('{"a": 1}');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\": 1}"]) == "text:{\"a\":1}"
-- select json_set('{"a":1}','$.a',1,'$.b',2,'$.c',3);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.a", T.i (1), T.t "$.b", T.i (2), T.t "$.c", T.i (3)]) == "text:{\"a\":1,\"b\":2,\"c\":3}"
-- select json_set('bad','$.a',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "bad", T.t "$.a", T.i (1)]) == "E:malformed JSON"
-- select json_set('{"a":[1,2]}','$.a[1]',9);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":[1,2]}", T.t "$.a[1]", T.i (9)]) == "text:{\"a\":[1,9]}"
-- select json_set('{"a":1}','$.a[0]',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.a[0]", T.i (2)]) == "text:{\"a\":1}"
-- select json_set('[1]','$.a',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1]", T.t "$.a", T.i (2)]) == "text:[1]"
-- select json_set('[1]','$[a]',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[1]", T.t "$[a]", T.i (2)]) == "E:bad JSON path: '$[a]'"
-- select json_set('{}','$.a.',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a.", T.i (2)]) == "E:bad JSON path: '$.a.'"
-- select json_set('{}','$.',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.", T.i (2)]) == "E:bad JSON path: '$.'"
-- select json_set('{}','$[',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$[", T.i (2)]) == "text:{}"
-- select json_set('1','$',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "1", T.t "$", T.i (2)]) == "text:2"
-- select json_set('{"a":1,"a":2}','$.a',3);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1,\"a\":2}", T.t "$.a", T.i (3)]) == "text:{\"a\":3,\"a\":2}"
-- select json_set('{}','$.é',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.é", T.i (1)]) == "text:{\"é\":1}"
-- select json_insert('{"a":1}','$.a',2);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{\"a\":1}", T.t "$.a", T.i (2)]) == "text:{\"a\":1}"
-- select json_insert('{"a":1}','$.b',2);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{\"a\":1}", T.t "$.b", T.i (2)]) == "text:{\"a\":1,\"b\":2}"
-- select json_insert('[1]','$[1]',2);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "[1]", T.t "$[1]", T.i (2)]) == "text:[1,2]"
-- select json_insert('[1]','$[0]',2);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "[1]", T.t "$[0]", T.i (2)]) == "text:[1]"
-- select json_insert('[1]','$',2);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "[1]", T.t "$", T.i (2)]) == "text:[1]"
-- select json_insert('{"a":1}','$.b.c',2);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{\"a\":1}", T.t "$.b.c", T.i (2)]) == "text:{\"a\":1,\"b\":{\"c\":2}}"
-- select json_insert('{"a":1}','$.b',json_array(1,2));
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{\"a\":1}", T.t "$.b", T.c "JSON_ARRAY" #[T.i (1), T.i (2)]]) == "text:{\"a\":1,\"b\":[1,2]}"
-- select json_insert('{"a":[1]}','$.a[#]',9);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{\"a\":[1]}", T.t "$.a[#]", T.i (9)]) == "text:{\"a\":[1,9]}"
-- select json_insert('{}','$.a','x','$.a','y');
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{}", T.t "$.a", T.t "x", T.t "$.a", T.t "y"]) == "text:{\"a\":\"x\"}"
-- select json_replace('{"a":1}','$.a',2);
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{\"a\":1}", T.t "$.a", T.i (2)]) == "text:{\"a\":2}"
-- select json_replace('{"a":1}','$.b',2);
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{\"a\":1}", T.t "$.b", T.i (2)]) == "text:{\"a\":1}"
-- select json_replace('[1,2]','$[1]',9);
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "[1,2]", T.t "$[1]", T.i (9)]) == "text:[1,9]"
-- select json_replace('[1,2]','$[2]',9);
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "[1,2]", T.t "$[2]", T.i (9)]) == "text:[1,2]"
-- select json_replace('{"a":1}','$',5);
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{\"a\":1}", T.t "$", T.i (5)]) == "text:5"
-- select json_replace('{"a":{"b":1}}','$.a.b','x');
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{\"a\":{\"b\":1}}", T.t "$.a.b", T.t "x"]) == "text:{\"a\":{\"b\":\"x\"}}"
-- select json_replace('{"a":1}','$.a','x','$.a','y');
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{\"a\":1}", T.t "$.a", T.t "x", T.t "$.a", T.t "y"]) == "text:{\"a\":\"y\"}"
-- select json_array_insert('[1,2]','$[1]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,2]", T.t "$[1]", T.i (9)]) == "text:[1,9,2]"
-- select json_array_insert('[1,2]','$[0]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,2]", T.t "$[0]", T.i (9)]) == "text:[9,1,2]"
-- select json_array_insert('[1,2]','$[2]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,2]", T.t "$[2]", T.i (9)]) == "text:[1,2,9]"
-- select json_array_insert('[1,2]','$[3]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,2]", T.t "$[3]", T.i (9)]) == "text:[1,2]"
-- select json_array_insert('[1,2]','$[#]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,2]", T.t "$[#]", T.i (9)]) == "text:[1,2,9]"
-- select json_array_insert('[1,2]','$',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,2]", T.t "$", T.i (9)]) == "text:[1,2]"
-- select json_array_insert('{"a":1}','$.a',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "{\"a\":1}", T.t "$.a", T.i (9)]) == "E:not an array element: '$.a'"
-- select json_array_insert('{"a":[1]}','$.a[0]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "{\"a\":[1]}", T.t "$.a[0]", T.i (9)]) == "text:{\"a\":[9,1]}"
-- select json_array_insert('{"a":[1]}','$.b[0]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "{\"a\":[1]}", T.t "$.b[0]", T.i (9)]) == "text:{\"a\":[1],\"b\":[9]}"
-- select json_array_insert('{"a":[1]}','$.b',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "{\"a\":[1]}", T.t "$.b", T.i (9)]) == "E:not an array element: '$.b'"
-- select json_remove('{"a":1,"b":2}','$.a');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":1,\"b\":2}", T.t "$.a"]) == "text:{\"b\":2}"
-- select json_remove('{"a":1,"b":2}','$.b');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":1,\"b\":2}", T.t "$.b"]) == "text:{\"a\":1}"
-- select json_remove('{"a":1,"b":2}','$.c');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":1,\"b\":2}", T.t "$.c"]) == "text:{\"a\":1,\"b\":2}"
-- select json_remove('[1,2,3]','$[1]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.t "$[1]"]) == "text:[1,3]"
-- select json_remove('[1,2,3]','$[0]','$[0]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.t "$[0]", T.t "$[0]"]) == "text:[3]"
-- select json_remove('[1,2,3]','$[#-1]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.t "$[#-1]"]) == "text:[1,2]"
-- select json_remove('[1,2,3]','$[5]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.t "$[5]"]) == "text:[1,2,3]"
-- select json_remove('[1,2,3]','$');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.t "$"]) == "null:"
-- select json_remove('[1,2,3]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]"]) == "text:[1,2,3]"
-- select json_remove('[1,2,3]',NULL);
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.n]) == "null:"
-- select json_remove(NULL,'$[0]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.n, T.t "$[0]"]) == "null:"
-- select json_remove('[1,2,3]','a');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.t "a"]) == "E:bad JSON path: 'a'"
-- select json_remove('{"a":{"b":1,"c":2}}','$.a.b');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":{\"b\":1,\"c\":2}}", T.t "$.a.b"]) == "text:{\"a\":{\"c\":2}}"
-- select json_remove('{"a":[1,2]}','$.a[0]','$.a[0]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":[1,2]}", T.t "$.a[0]", T.t "$.a[0]"]) == "text:{\"a\":[]}"
-- select json_remove('{"a":1}','$.a','$.a');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":1}", T.t "$.a", T.t "$.a"]) == "text:{}"
-- select json_remove('{ "a" : 1 }');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{ \"a\" : 1 }"]) == "text:{\"a\":1}"
-- select json_remove();
#guard TJ.show' (T.c "JSON_REMOVE" #[]) == "null:"
-- select json_remove('[1]','$[');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1]", T.t "$["]) == "E:bad JSON path: '$['"
-- select json_patch('{"a":1,"b":2}','{"a":9,"c":3}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1,\"b\":2}", T.t "{\"a\":9,\"c\":3}"]) == "text:{\"a\":9,\"b\":2,\"c\":3}"
-- select json_patch('{"a":1,"b":2}','{"a":null}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1,\"b\":2}", T.t "{\"a\":null}"]) == "text:{\"b\":2}"
-- select json_patch('{"a":{"b":1}}','{"a":{"c":2}}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":{\"b\":1}}", T.t "{\"a\":{\"c\":2}}"]) == "text:{\"a\":{\"b\":1,\"c\":2}}"
-- select json_patch('{"a":1}','[1,2]');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "[1,2]"]) == "text:[1,2]"
-- select json_patch('[1,2]','{"a":1}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "[1,2]", T.t "{\"a\":1}"]) == "text:{\"a\":1}"
-- select json_patch('{"a":1}','5');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "5"]) == "text:5"
-- select json_patch('{"a":1}','null');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "null"]) == "text:null"
-- select json_patch('{}','{"a":{"b":null,"c":1}}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{}", T.t "{\"a\":{\"b\":null,\"c\":1}}"]) == "text:{\"a\":{\"c\":1}}"
-- select json_patch('{"a":[1,2]}','{"a":[3]}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":[1,2]}", T.t "{\"a\":[3]}"]) == "text:{\"a\":[3]}"
-- select json_patch('{"a":1}',NULL);
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.n]) == "null:"
-- select json_patch(NULL,'{}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.n, T.t "{}"]) == "null:"
-- select json_patch('{"a":1}','bad');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "bad"]) == "E:malformed JSON"
-- select json_patch('bad','{}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "bad", T.t "{}"]) == "E:malformed JSON"
-- select json_patch('{"a":1,"b":2}','{"b":null,"a":null}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1,\"b\":2}", T.t "{\"b\":null,\"a\":null}"]) == "text:{}"
-- select json_patch('{"a":1}','{"b":{}}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "{\"b\":{}}"]) == "text:{\"a\":1,\"b\":{}}"
-- select json_patch('{"a":1}','{}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "{}"]) == "text:{\"a\":1}"
-- select json_pretty('[1,{"a":[],"b":{},"c":[1,2,{"d":null}]}]');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "[1,{\"a\":[],\"b\":{},\"c\":[1,2,{\"d\":null}]}]"]) == "text:[\x0a    1,\x0a    {\x0a        \"a\": [],\x0a        \"b\": {},\x0a        \"c\": [\x0a            1,\x0a            2,\x0a            {\x0a                \"d\": null\x0a            }\x0a        ]\x0a    }\x0a]"
-- select json_pretty('{}');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "{}"]) == "text:{}"
-- select json_pretty('[]');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "[]"]) == "text:[]"
-- select json_pretty('1');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "1"]) == "text:1"
-- select json_pretty('"a"');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "\"a\""]) == "text:\"a\""
-- select json_pretty('[1,2]','  ');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "[1,2]", T.t "  "]) == "text:[\x0a  1,\x0a  2\x0a]"
-- select json_pretty('[1,2]','	');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "[1,2]", T.t "\x09"]) == "text:[\x0a\x091,\x0a\x092\x0a]"
-- select json_pretty('[1,2]','');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "[1,2]", T.t ""]) == "text:[\x0a1,\x0a2\x0a]"
-- select json_pretty('[1,2]',NULL);
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "[1,2]", T.n]) == "text:[\x0a    1,\x0a    2\x0a]"
-- select json_pretty('{"a":{"b":{"c":1}}}','--');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "{\"a\":{\"b\":{\"c\":1}}}", T.t "--"]) == "text:{\x0a--\"a\": {\x0a----\"b\": {\x0a------\"c\": 1\x0a----}\x0a--}\x0a}"
-- select json_pretty(NULL);
#guard TJ.show' (T.c "JSON_PRETTY" #[T.n]) == "null:"
-- select json_pretty('bad');
#guard TJ.show' (T.c "JSON_PRETTY" #[T.t "bad"]) == "E:malformed JSON"
-- select json();
#guard TJ.show' (T.c "JSON" #[]) == "E:wrong number of arguments to function json()"
-- select json(1,2);
#guard TJ.show' (T.c "JSON" #[T.i (1), T.i (2)]) == "E:wrong number of arguments to function json()"
-- select json_array_length('[1]',1,2);
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[1]", T.i (1), T.i (2)]) == "E:wrong number of arguments to function json_array_length()"
-- select json_quote();
#guard TJ.show' (T.c "JSON_QUOTE" #[]) == "E:wrong number of arguments to function json_quote()"
-- select json_patch('{}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{}"]) == "E:wrong number of arguments to function json_patch()"
-- select json_valid();
#guard TJ.show' (T.c "JSON_VALID" #[]) == "E:wrong number of arguments to function json_valid()"
-- select json_type();
#guard TJ.show' (T.c "JSON_TYPE" #[]) == "E:wrong number of arguments to function json_type()"
-- select json_error_position();
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[]) == "E:wrong number of arguments to function json_error_position()"
-- select json_set();
#guard TJ.show' (T.c "JSON_SET" #[]) == "null:"
-- select json_insert('{}','$.a');
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{}", T.t "$.a"]) == "E:json_insert() needs an odd number of arguments"
-- select json_replace('{}','$.a');
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{}", T.t "$.a"]) == "E:json_replace() needs an odd number of arguments"
-- select json_array_insert('[]','$[0]');
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[]", T.t "$[0]"]) == "E:json_array_insert() needs an odd number of arguments"
-- select json_extract();
#guard TJ.show' (T.c "JSON_EXTRACT" #[]) == "null:"
-- select json('{a:1,b:2,"c":3}');
#guard TJ.show' (T.c "JSON" #[T.t "{a:1,b:2,\"c\":3}"]) == "text:{\"a\":1,\"b\":2,\"c\":3}"
-- select json('{$a:1,_b:2,c1:3}');
#guard TJ.show' (T.c "JSON" #[T.t "{$a:1,_b:2,c1:3}"]) == "text:{\"$a\":1,\"_b\":2,\"c1\":3}"
-- select json('{a:1,}');
#guard TJ.show' (T.c "JSON" #[T.t "{a:1,}"]) == "text:{\"a\":1}"
-- select json('{ a : 1 }');
#guard TJ.show' (T.c "JSON" #[T.t "{ a : 1 }"]) == "text:{\"a\":1}"
-- select json('{if:1}');
#guard TJ.show' (T.c "JSON" #[T.t "{if:1}"]) == "text:{\"if\":1}"
-- select json('{true:1}');
#guard TJ.show' (T.c "JSON" #[T.t "{true:1}"]) == "E:malformed JSON"
-- select json('{1a:1}');
#guard TJ.show' (T.c "JSON" #[T.t "{1a:1}"]) == "E:malformed JSON"
-- select json('{a b:1}');
#guard TJ.show' (T.c "JSON" #[T.t "{a b:1}"]) == "E:malformed JSON"
-- select json('{é:1}');
#guard TJ.show' (T.c "JSON" #[T.t "{é:1}"]) == "text:{\"é\":1}"
-- select json('[1,/*c*/2]');
#guard TJ.show' (T.c "JSON" #[T.t "[1,/*c*/2]"]) == "text:[1,2]"
-- select json('[1,2]//c');
#guard TJ.show' (T.c "JSON" #[T.t "[1,2]//c"]) == "text:[1,2]"
-- select json('// c'||char(10)||'[1]');
#guard TJ.show' (T.c "JSON" #[T.t "// c\x0a[1]"]) == "text:[1]"
-- select json('/* a */ [1] /* b */');
#guard TJ.show' (T.c "JSON" #[T.t "/* a */ [1] /* b */"]) == "text:[1]"
-- select json('[1 /*x*/ , 2]');
#guard TJ.show' (T.c "JSON" #[T.t "[1 /*x*/ , 2]"]) == "text:[1,2]"
-- select json('[1,2 /*x*/ ]');
#guard TJ.show' (T.c "JSON" #[T.t "[1,2 /*x*/ ]"]) == "text:[1,2]"
-- select json('{"a" /*x*/ : 1}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\" /*x*/ : 1}"]) == "text:{\"a\":1}"
-- select json('/*');
#guard TJ.show' (T.c "JSON" #[T.t "/*"]) == "E:malformed JSON"
-- select json('[1]/');
#guard TJ.show' (T.c "JSON" #[T.t "[1]/"]) == "E:malformed JSON"
-- select json('[1] /');
#guard TJ.show' (T.c "JSON" #[T.t "[1] /"]) == "E:malformed JSON"
-- select json('''abc''');
#guard TJ.show' (T.c "JSON" #[T.t "'abc'"]) == "text:\"abc\""
-- select json('[''a'',"b"]');
#guard TJ.show' (T.c "JSON" #[T.t "['a',\"b\"]"]) == "text:[\"a\",\"b\"]"
-- select json('[''a"b'']');
#guard TJ.show' (T.c "JSON" #[T.t "['a\"b']"]) == "text:[\"a\\\"b\"]"
-- select json('''a\''b''');
#guard TJ.show' (T.c "JSON" #[T.t "'a\\'b'"]) == "text:\"a'b\""
-- select json('"a\''b"');
#guard TJ.show' (T.c "JSON" #[T.t "\"a\\'b\""]) == "text:\"a'b\""
-- select json('"\v"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\v\""]) == "text:\"\\u000b\""
-- select json('"\0"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\0\""]) == "text:\"\\u0000\""
-- select json('"\x41\x7a"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\x41\\x7a\""]) == "text:\"\\u0041\\u007a\""
-- select json('"a\'||char(10)||'b"');
#guard TJ.show' (T.c "JSON" #[T.t "\"a\\\x0ab\""]) == "text:\"ab\""
-- select json('"\q"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\q\""]) == "E:malformed JSON"
-- select json('"\u12"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\u12\""]) == "E:malformed JSON"
-- select json('"\u00zz"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\u00zz\""]) == "E:malformed JSON"
-- select json('"\00"');
#guard TJ.show' (T.c "JSON" #[T.t "\"\\00\""]) == "E:malformed JSON"
-- select json_extract('"\x41\''"','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "\"\\x41\\'\"", T.t "$"]) == "text:A'"
-- select json_extract('''a"b''','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "'a\"b'", T.t "$"]) == "text:a\"b"
-- select json_extract('"\v"','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "\"\\v\"", T.t "$"]) == "text:\x0b"
-- select json_extract('"a\'||char(10)||'b"','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "\"a\\\x0ab\"", T.t "$"]) == "text:ab"
-- select json_extract('{''k\x41'':1}','$.kA');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{'k\\x41':1}", T.t "$.kA"]) == "integer:1"
-- select json('[0x1F,0XfF,-0x1,+0x2,0x7fffffffffffffff,0xffffffffffffffff,0x10000000000000000]');
#guard TJ.show' (T.c "JSON" #[T.t "[0x1F,0XfF,-0x1,+0x2,0x7fffffffffffffff,0xffffffffffffffff,0x10000000000000000]"]) == "text:[31,255,-1,2,9223372036854775807,18446744073709551615,9.0e999]"
-- select json('[+1,+1.5,+.5,-.5,.5e3,5.e3,5.E-3,+Inf,-inf,+Infinity,-Infinity,Infinity,inf,NaN,nan,QNaN,SNaN]');
#guard TJ.show' (T.c "JSON" #[T.t "[+1,+1.5,+.5,-.5,.5e3,5.e3,5.E-3,+Inf,-inf,+Infinity,-Infinity,Infinity,inf,NaN,nan,QNaN,SNaN]"]) == "text:[1,1.5,0.5,-0.5,0.5e3,5.0e3,5.0E-3,9e999,-9e999,9e999,-9e999,9e999,9e999,null,null,null,null]"
-- select json('[1e5,1E5,1e+5,1e-5,0.5,-0.5,0e0,0.0,-0.0,0]');
#guard TJ.show' (T.c "JSON" #[T.t "[1e5,1E5,1e+5,1e-5,0.5,-0.5,0e0,0.0,-0.0,0]"]) == "text:[1e5,1E5,1e+5,1e-5,0.5,-0.5,0e0,0.0,-0.0,0]"
-- select json('[00]');
#guard TJ.show' (T.c "JSON" #[T.t "[00]"]) == "E:malformed JSON"
-- select json('[0123]');
#guard TJ.show' (T.c "JSON" #[T.t "[0123]"]) == "E:malformed JSON"
-- select json('[1.]');
#guard TJ.show' (T.c "JSON" #[T.t "[1.]"]) == "text:[1.0]"
-- select json('[.]');
#guard TJ.show' (T.c "JSON" #[T.t "[.]"]) == "E:malformed JSON"
-- select json('[1e]');
#guard TJ.show' (T.c "JSON" #[T.t "[1e]"]) == "E:malformed JSON"
-- select json('[1e5.5]');
#guard TJ.show' (T.c "JSON" #[T.t "[1e5.5]"]) == "E:malformed JSON"
-- select json('[--1]');
#guard TJ.show' (T.c "JSON" #[T.t "[--1]"]) == "E:malformed JSON"
-- select json('[+-1]');
#guard TJ.show' (T.c "JSON" #[T.t "[+-1]"]) == "E:malformed JSON"
-- select json('[+]');
#guard TJ.show' (T.c "JSON" #[T.t "[+]"]) == "E:malformed JSON"
-- select json('[0x]');
#guard TJ.show' (T.c "JSON" #[T.t "[0x]"]) == "E:malformed JSON"
-- select json('[0xg]');
#guard TJ.show' (T.c "JSON" #[T.t "[0xg]"]) == "E:malformed JSON"
-- select json('[1.2e]');
#guard TJ.show' (T.c "JSON" #[T.t "[1.2e]"]) == "E:malformed JSON"
-- select json('[-Infinit]');
#guard TJ.show' (T.c "JSON" #[T.t "[-Infinit]"]) == "E:malformed JSON"
-- select json('[NaNa]');
#guard TJ.show' (T.c "JSON" #[T.t "[NaNa]"]) == "E:malformed JSON"
-- select json('[infinit]');
#guard TJ.show' (T.c "JSON" #[T.t "[infinit]"]) == "E:malformed JSON"
-- select json('[Infinityx]');
#guard TJ.show' (T.c "JSON" #[T.t "[Infinityx]"]) == "E:malformed JSON"
-- select json('[1,2,3,]');
#guard TJ.show' (T.c "JSON" #[T.t "[1,2,3,]"]) == "text:[1,2,3]"
-- select json('[,1]');
#guard TJ.show' (T.c "JSON" #[T.t "[,1]"]) == "E:malformed JSON"
-- select json('[1,,]');
#guard TJ.show' (T.c "JSON" #[T.t "[1,,]"]) == "E:malformed JSON"
-- select json('{"a":1,,}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\":1,,}"]) == "E:malformed JSON"
-- select json('{,"a":1}');
#guard TJ.show' (T.c "JSON" #[T.t "{,\"a\":1}"]) == "E:malformed JSON"
-- select json('[1,]]');
#guard TJ.show' (T.c "JSON" #[T.t "[1,]]"]) == "E:malformed JSON"
-- select json('[[]]');
#guard TJ.show' (T.c "JSON" #[T.t "[[]]"]) == "text:[[]]"
-- select json('[[],{}]');
#guard TJ.show' (T.c "JSON" #[T.t "[[],{}]"]) == "text:[[],{}]"
-- select json('{"a":{}}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\":{}}"]) == "text:{\"a\":{}}"
-- select json('{"a":[]}');
#guard TJ.show' (T.c "JSON" #[T.t "{\"a\":[]}"]) == "text:{\"a\":[]}"
-- select json('  {  }  ');
#guard TJ.show' (T.c "JSON" #[T.t "  {  }  "]) == "text:{}"
-- select json_valid('[1,2,3,]',1);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[1,2,3,]", T.i (1)]) == "integer:0"
-- select json_valid('{"a":1,}',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{\"a\":1,}", T.i (2)]) == "integer:1"
-- select json_valid('{''a'':1}');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{'a':1}"]) == "integer:0"
-- select json_valid('{''a'':1}',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{'a':1}", T.i (2)]) == "integer:1"
-- select json_valid('// x'||char(10)||'1',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "// x\x0a1", T.i (2)]) == "integer:1"
-- select json_valid('[1] // x',1);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[1] // x", T.i (1)]) == "integer:0"
-- select json_valid(char(12)||'1',1);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "\x0c1", T.i (1)]) == "integer:0"
-- select json_valid(char(12)||'1',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "\x0c1", T.i (2)]) == "integer:1"
-- select json_valid('[Infinity]',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[Infinity]", T.i (2)]) == "integer:1"
-- select json_valid('[+1]');
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[+1]"]) == "integer:0"
-- select json_valid('[+1]',2);
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[+1]", T.i (2)]) == "integer:1"
-- select json_error_position('{"a":1,}x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":1,}x"]) == "integer:8"
-- select json_error_position('[] x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[] x"]) == "integer:2"
-- select json_error_position('[1,] x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1,] x"]) == "integer:4"
-- select json_error_position('{} x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{} x"]) == "integer:2"
-- select json_error_position('[1,2] x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1,2] x"]) == "integer:1"
-- select json_error_position('[[]] x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[[]] x"]) == "integer:3"
-- select json_error_position('[[],[1,]] x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[[],[1,]] x"]) == "integer:8"
-- select json_error_position('1 x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "1 x"]) == "integer:1"
-- select json_error_position('{a b:1}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{a b:1}"]) == "integer:4"
-- select json_error_position('{a:}');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{a:}"]) == "integer:4"
-- select json_error_position('[''a]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "['a]"]) == "integer:5"
-- select json_error_position('["\q"]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[\"\\q\"]"]) == "integer:4"
-- select json_error_position('["é\q"]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[\"é\\q\"]"]) == "integer:5"
-- select json_error_position('[00]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[00]"]) == "integer:3"
-- select json_error_position('[0x]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[0x]"]) == "integer:3"
-- select json_error_position('[+]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[+]"]) == "integer:2"
-- select json_error_position('{"a":1 /* x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "{\"a\":1 /* x"]) == "integer:8"
-- select json_error_position('/* x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "/* x"]) == "integer:1"
-- select json_error_position('[1 /* x');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1 /* x"]) == "integer:4"
-- select json_error_position('[1 2 /* x */]');
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[1 2 /* x */]"]) == "integer:4"
-- select json_set('{}','$.a','x"y');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "x\"y"]) == "text:{\"a\":\"x\\\"y\"}"
-- select json_set('{}','$.a','a'||char(10)||'b');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "a\x0ab"]) == "text:{\"a\":\"a\\nb\"}"
-- select json_set('{}','$.a','é');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "é"]) == "text:{\"a\":\"é\"}"
-- select json_set('{}','$.a',''||char(1));
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "\x01"]) == "text:{\"a\":\"\\u0001\"}"
-- select json_set('{}','$.a','\');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "\\"]) == "text:{\"a\":\"\\\\\"}"
-- select json_set('{}','$.a','/');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "/"]) == "text:{\"a\":\"/\"}"
-- select json_quote('é€😀');
#guard TJ.show' (T.c "JSON_QUOTE" #[T.t "é€😀"]) == "text:\"é€😀\""
-- select json_quote('');
#guard TJ.show' (T.c "JSON_QUOTE" #[T.t ""]) == "text:\"\""
-- select json_quote(0);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.i (0)]) == "text:0"
-- select json_quote(-1);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.i (-1)]) == "text:-1"
-- select json_quote(9223372036854775807);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.i (9223372036854775807)]) == "text:9223372036854775807"
-- select json_quote(1e15);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (1.0e15)]) == "text:1000000000000000.0"
-- select json_quote(1e16);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (1.0e16)]) == "text:10000000000000000.0"
-- select json_quote(0.5);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (0.5)]) == "text:0.5"
-- select json_quote(100.0);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (100.0)]) == "text:100.0"
-- select json_quote(1e-5);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (1.0e-5)]) == "text:1.0e-05"
-- select json_quote(123456.789e3);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (123456.789e3)]) == "text:123456789.0"
-- select json_quote(3.14159265358979);
#guard TJ.show' (T.c "JSON_QUOTE" #[T.r (3.14159265358979)]) == "text:3.14159265358979"
-- select json_array(1e100,1e-100,5e-324,1.7976931348623157e308);
#guard TJ.show' (T.c "JSON_ARRAY" #[T.r (1.0e100), T.r (1.0e-100), T.r (5.0e-324), T.r (1.7976931348623157e308)]) == "text:[1.0e+100,1.0e-100,4.9406564584124654e-324,1.7976931348623157e+308]"
-- select json_object('a',1,'a',2);
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "a", T.i (1), T.t "a", T.i (2)]) == "text:{\"a\":1,\"a\":2}"
-- select json_object('',1);
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "", T.i (1)]) == "text:{\"\":1}"
-- select json_object('x',json_object('y',json_array(1,2)));
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "x", T.c "JSON_OBJECT" #[T.t "y", T.c "JSON_ARRAY" #[T.i (1), T.i (2)]]]) == "text:{\"x\":{\"y\":[1,2]}}"
-- select json_object('x','{"y":1}');
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "x", T.t "{\"y\":1}"]) == "text:{\"x\":\"{\\\"y\\\":1}\"}"
-- select json_array(json_array());
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_ARRAY" #[]]) == "text:[[]]"
-- select json_array(json('{"a":1}'),json('[]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON" #[T.t "{\"a\":1}"], T.c "JSON" #[T.t "[]"]]) == "text:[{\"a\":1},[]]"
-- select json_quote(json_object('a',1));
#guard TJ.show' (T.c "JSON_QUOTE" #[T.c "JSON_OBJECT" #[T.t "a", T.i (1)]]) == "text:{\"a\":1}"
-- select json_extract('[1,2,3]','$[1]','$[2]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2,3]", T.t "$[1]", T.t "$[2]"]) == "text:[2,3]"
-- select json_extract('{"a":{"b":1}}','$.a','$.a.b');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":{\"b\":1}}", T.t "$.a", T.t "$.a.b"]) == "text:[{\"b\":1},1]"
-- select json_extract('{"a":"x"}','$.a','$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":\"x\"}", T.t "$.a", T.t "$.a"]) == "text:[\"x\",\"x\"]"
-- select json_extract('{"a":"x"}','$','$');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":\"x\"}", T.t "$", T.t "$"]) == "text:[{\"a\":\"x\"},{\"a\":\"x\"}]"
-- select json_extract(json('{"a":[1,2]}'),'$.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.c "JSON" #[T.t "{\"a\":[1,2]}"], T.t "$.a"]) == "text:[1,2]"
-- select json_type(json_extract('{"a":[1]}','$.a'));
#guard TJ.show' (T.c "JSON_TYPE" #[T.c "JSON_EXTRACT" #[T.t "{\"a\":[1]}", T.t "$.a"]]) == "text:array"
-- select json_extract('[1,2]',1);
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[1,2]", T.i (1)]) == "E:bad JSON path: '1'"
-- select json_extract('{"1":2}','$.1');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"1\":2}", T.t "$.1"]) == "integer:2"
-- select json_extract('{"a":1}', '$ .a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t "$ .a"]) == "E:bad JSON path: '$ .a'"
-- select json_extract('{"a":1}', ' $.a');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":1}", T.t " $.a"]) == "E:bad JSON path: ' $.a'"
-- select json_extract('[[1,2],[3,4]]','$[1][0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[[1,2],[3,4]]", T.t "$[1][0]"]) == "integer:3"
-- select json_extract('[[1,2],[3,4]]','$[1][#-1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[[1,2],[3,4]]", T.t "$[1][#-1]"]) == "integer:4"
-- select json_extract('[[1,2],[3,4]]','$[#-1][#-1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[[1,2],[3,4]]", T.t "$[#-1][#-1]"]) == "integer:4"
-- select json_extract('{"a":[{"b":1},{"b":2}]}','$.a[1].b');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "{\"a\":[{\"b\":1},{\"b\":2}]}", T.t "$.a[1].b"]) == "integer:2"
-- select '{"a":1}' -> 'a' -> 'b';
#guard TJ.show' (T.c "->" #[T.c "->" #[T.t "{\"a\":1}", T.t "a"], T.t "b"]) == "null:"
-- select '[{"a":1}]' -> 0 ->> 'a';
#guard TJ.show' (T.c "->>" #[T.c "->" #[T.t "[{\"a\":1}]", T.i (0)], T.t "a"]) == "integer:1"
-- select '{"a":[1,2,3]}' -> 'a' -> -1;
#guard TJ.show' (T.c "->" #[T.c "->" #[T.t "{\"a\":[1,2,3]}", T.t "a"], T.i (-1)]) == "text:3"
-- select '{"a":[1,2,3]}' -> 'a' ->> -3;
#guard TJ.show' (T.c "->>" #[T.c "->" #[T.t "{\"a\":[1,2,3]}", T.t "a"], T.i (-3)]) == "integer:1"
-- select '{"a":[1,2,3]}' -> 'a' ->> -4;
#guard TJ.show' (T.c "->>" #[T.c "->" #[T.t "{\"a\":[1,2,3]}", T.t "a"], T.i (-4)]) == "null:"
-- select '{"0":5}' -> 0;
#guard TJ.show' (T.c "->" #[T.t "{\"0\":5}", T.i (0)]) == "null:"
-- select '{"0":5}' -> '0';
#guard TJ.show' (T.c "->" #[T.t "{\"0\":5}", T.t "0"]) == "text:5"
-- select '{"a":1}' -> '.a';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":1}", T.t ".a"]) == "null:"
-- select '{"a":1}' -> 'a.b';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":1}", T.t "a.b"]) == "null:"
-- select '{"a":{"b":2}}' -> 'a.b';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":{\"b\":2}}", T.t "a.b"]) == "null:"
-- select '[1,2]' -> '[0]';
#guard TJ.show' (T.c "->" #[T.t "[1,2]", T.t "[0]"]) == "text:1"
-- select '[1,2]' -> '[#-1]';
#guard TJ.show' (T.c "->" #[T.t "[1,2]", T.t "[#-1]"]) == "text:2"
-- select '[1,2]' -> '[]';
#guard TJ.show' (T.c "->" #[T.t "[1,2]", T.t "[]"]) == "null:"
-- select '[1,2]' -> '[x]';
#guard TJ.show' (T.c "->" #[T.t "[1,2]", T.t "[x]"]) == "E:bad JSON path: '[x]'"
-- select '{"a":1}' ->> 'a' ->> 'b';
#guard TJ.show' (T.c "->>" #[T.c "->>" #[T.t "{\"a\":1}", T.t "a"], T.t "b"]) == "null:"
-- select '{"a":"[1]"}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":\"[1]\"}", T.t "a"]) == "text:[1]"
-- select '{"a":"[1]"}' -> 'a';
#guard TJ.show' (T.c "->" #[T.t "{\"a\":\"[1]\"}", T.t "a"]) == "text:\"[1]\""
-- select '{"a":12345678901234567890}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":12345678901234567890}", T.t "a"]) == "real:1.2345678901234567e+19"
-- select '{"a":1e400}' ->> 'a';
#guard TJ.show' (T.c "->>" #[T.t "{\"a\":1e400}", T.t "a"]) == "real:Inf"
-- select json_patch('{"a":{"b":1,"c":2}}','{"a":{"b":null}}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":{\"b\":1,\"c\":2}}", T.t "{\"a\":{\"b\":null}}"]) == "text:{\"a\":{\"c\":2}}"
-- select json_patch('{"a":1}','{"a":{"b":null}}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "{\"a\":{\"b\":null}}"]) == "text:{\"a\":{}}"
-- select json_patch('{"a":[1]}','{"b":[null]}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":[1]}", T.t "{\"b\":[null]}"]) == "text:{\"a\":[1],\"b\":[null]}"
-- select json_patch('[1]','[2]');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "[1]", T.t "[2]"]) == "text:[2]"
-- select json_patch('1','2');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "1", T.t "2"]) == "text:2"
-- select json_patch('{"a":1}','{"a":null,"a":2}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1}", T.t "{\"a\":null,\"a\":2}"]) == "text:{\"a\":2}"
-- select json_patch('{"a":1,"a":2}','{"a":3}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"a\":1,\"a\":2}", T.t "{\"a\":3}"]) == "text:{\"a\":3,\"a\":2}"
-- select json_patch('{}','{"a":{"b":{"c":null}}}');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{}", T.t "{\"a\":{\"b\":{\"c\":null}}}"]) == "text:{\"a\":{\"b\":{}}}"
-- select json_patch('{"x":1}','"s"');
#guard TJ.show' (T.c "JSON_PATCH" #[T.t "{\"x\":1}", T.t "\"s\""]) == "text:\"s\""
-- select json_remove('{"a":[1,2,3]}','$.a[1]','$.a[1]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":[1,2,3]}", T.t "$.a[1]", T.t "$.a[1]"]) == "text:{\"a\":[1]}"
-- select json_remove('[[1,2],[3]]','$[0][0]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[[1,2],[3]]", T.t "$[0][0]"]) == "text:[[2],[3]]"
-- select json_remove('[1,2,3]','$[#-1]','$[#-1]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2,3]", T.t "$[#-1]", T.t "$[#-1]"]) == "text:[1]"
-- select json_remove('{"a":{"b":1}}','$.a');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":{\"b\":1}}", T.t "$.a"]) == "text:{}"
-- select json_remove('{"a":1}','$.a.b');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":1}", T.t "$.a.b"]) == "text:{\"a\":1}"
-- select json_remove('{"a":1}','$[0]');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":1}", T.t "$[0]"]) == "text:{\"a\":1}"
-- select json_remove('[1,2]','$.a');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "[1,2]", T.t "$.a"]) == "text:[1,2]"
-- select json_remove('{"a":1}','$."a"');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a\":1}", T.t "$.\"a\""]) == "text:{}"
-- select json_remove('{"a b":1,"c":2}','$."a b"');
#guard TJ.show' (T.c "JSON_REMOVE" #[T.t "{\"a b\":1,\"c\":2}", T.t "$.\"a b\""]) == "text:{\"c\":2}"
-- select json_set('[]','$[0]',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[]", T.t "$[0]", T.i (1)]) == "text:[1]"
-- select json_set('[]','$[#]',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[]", T.t "$[#]", T.i (1)]) == "text:[1]"
-- select json_set('[]','$[1]',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[]", T.t "$[1]", T.i (1)]) == "text:[]"
-- select json_set('[]','$[#-1]',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[]", T.t "$[#-1]", T.i (1)]) == "text:[]"
-- select json_set('{}','$.a[0].b',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a[0].b", T.i (1)]) == "text:{\"a\":[{\"b\":1}]}"
-- select json_set('{}','$.a[#].b',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a[#].b", T.i (1)]) == "text:{\"a\":[{\"b\":1}]}"
-- select json_set('{"a":[]}','$.a[0].b',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":[]}", T.t "$.a[0].b", T.i (1)]) == "text:{\"a\":[{\"b\":1}]}"
-- select json_set('{"a":[{}]}','$.a[0].b',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":[{}]}", T.t "$.a[0].b", T.i (1)]) == "text:{\"a\":[{\"b\":1}]}"
-- select json_set('{"a":[{}]}','$.a[1].b',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":[{}]}", T.t "$.a[1].b", T.i (1)]) == "text:{\"a\":[{},{\"b\":1}]}"
-- select json_set('{"a":[{}]}','$.a[#].b',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":[{}]}", T.t "$.a[#].b", T.i (1)]) == "text:{\"a\":[{},{\"b\":1}]}"
-- select json_set('null','$.a',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "null", T.t "$.a", T.i (1)]) == "text:null"
-- select json_set('5','$[0]',1);
#guard TJ.show' (T.c "JSON_SET" #[T.t "5", T.t "$[0]", T.i (1)]) == "text:5"
-- select json_set('{}','$.a','1','$.a','2');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.t "1", T.t "$.a", T.t "2"]) == "text:{\"a\":\"2\"}"
-- select json_set('{}','$.a',1,NULL,2,'$.b',3);
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.i (1), T.n, T.i (2), T.t "$.b", T.i (3)]) == "text:{\"a\":1,\"b\":3}"
-- select json_set('{}','$.a',1,'$.b');
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.i (1), T.t "$.b"]) == "E:json_set() needs an odd number of arguments"
-- select json_set('{}','$.a',json('[1]'),'$.b',json('{}'));
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.c "JSON" #[T.t "[1]"], T.t "$.b", T.c "JSON" #[T.t "{}"]]) == "text:{\"a\":[1],\"b\":{}}"
-- select json_set('{"a":1}','$.a',json('null'));
#guard TJ.show' (T.c "JSON_SET" #[T.t "{\"a\":1}", T.t "$.a", T.c "JSON" #[T.t "null"]]) == "text:{\"a\":null}"
-- select json_insert('[1,2]','$[#]',3,'$[#]',4);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "[1,2]", T.t "$[#]", T.i (3), T.t "$[#]", T.i (4)]) == "text:[1,2,3,4]"
-- select json_insert('[]','$[0]',1);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "[]", T.t "$[0]", T.i (1)]) == "text:[1]"
-- select json_insert('{"a":{}}','$.a.b.c',1);
#guard TJ.show' (T.c "JSON_INSERT" #[T.t "{\"a\":{}}", T.t "$.a.b.c", T.i (1)]) == "text:{\"a\":{\"b\":{\"c\":1}}}"
-- select json_replace('{"a":[1,2]}','$.a',json('{"x":1}'));
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{\"a\":[1,2]}", T.t "$.a", T.c "JSON" #[T.t "{\"x\":1}"]]) == "text:{\"a\":{\"x\":1}}"
-- select json_replace('[]','$[0]',1);
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "[]", T.t "$[0]", T.i (1)]) == "text:[]"
-- select json_replace('{}','$.a.b',1);
#guard TJ.show' (T.c "JSON_REPLACE" #[T.t "{}", T.t "$.a.b", T.i (1)]) == "text:{}"
-- select json_array_insert('[]','$[0]',1);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[]", T.t "$[0]", T.i (1)]) == "text:[1]"
-- select json_array_insert('[]','$[#]',1);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[]", T.t "$[#]", T.i (1)]) == "text:[1]"
-- select json_array_insert('[1]','$[#-1]',0);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1]", T.t "$[#-1]", T.i (0)]) == "text:[0,1]"
-- select json_array_insert('[1,[2]]','$[1][0]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,[2]]", T.t "$[1][0]", T.i (9)]) == "text:[1,[9,2]]"
-- select json_array_insert('[1,[2]]','$[1][1]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1,[2]]", T.t "$[1][1]", T.i (9)]) == "text:[1,[2,9]]"
-- select json_array_insert('{"a":[1]}','$.a[1]',9);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "{\"a\":[1]}", T.t "$.a[1]", T.i (9)]) == "text:{\"a\":[1,9]}"
-- select json_array_insert('[1]','$[0]',1,'$[0]',2);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1]", T.t "$[0]", T.i (1), T.t "$[0]", T.i (2)]) == "text:[2,1,1]"
-- select json_array_insert('[1]','$[a]',1);
#guard TJ.show' (T.c "JSON_ARRAY_INSERT" #[T.t "[1]", T.t "$[a]", T.i (1)]) == "E:bad JSON path: '$[a]'"
-- select json_valid('[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[...
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]"]) == "integer:1"
-- select json_valid('[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[...
#guard TJ.show' (T.c "JSON_VALID" #[T.t "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]"]) == "integer:0"
-- select json_error_position('[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[...
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]"]) == "integer:1001"
-- select json_error_position('[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[...
#guard TJ.show' (T.c "JSON_ERROR_POSITION" #[T.t "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]"]) == "integer:1001"
-- select json_valid('{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a...
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":1}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}"]) == "integer:1"
-- select json_valid('{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a":{"a...
#guard TJ.show' (T.c "JSON_VALID" #[T.t "{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":{\"a\":1}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}"]) == "integer:0"
-- select json_type('[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[...
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]"]) == "text:array"
-- select json_array_length('[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[...
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]"]) == "integer:1"
-- select json_array_length('[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[...
#guard TJ.show' (T.c "JSON_ARRAY_LENGTH" #[T.t "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]"]) == "E:malformed JSON"
-- select json_extract('[0xffffffffffffffff]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[0xffffffffffffffff]", T.t "$[0]"]) == "real:1.8446744073709552e+19"
-- select json_extract('[0x8000000000000000]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[0x8000000000000000]", T.t "$[0]"]) == "real:9.2233720368547758e+18"
-- select json_extract('[-0x8000000000000000]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[-0x8000000000000000]", T.t "$[0]"]) == "real:-9.2233720368547758e+18"
-- select json_extract('[0x10000000000000000]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[0x10000000000000000]", T.t "$[0]"]) == "E:malformed JSON"
-- select json_extract('[0x7fffffffffffffff]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[0x7fffffffffffffff]", T.t "$[0]"]) == "integer:9223372036854775807"
-- select '[0xffffffffffffffff]' ->> 0;
#guard TJ.show' (T.c "->>" #[T.t "[0xffffffffffffffff]", T.i (0)]) == "real:1.8446744073709552e+19"
-- select '[0x1F]' -> 0;
#guard TJ.show' (T.c "->" #[T.t "[0x1F]", T.i (0)]) == "text:31"
-- select json_extract('[Infinity]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[Infinity]", T.t "$[0]"]) == "real:Inf"
-- select json_extract('[-Infinity]','$[0]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[-Infinity]", T.t "$[0]"]) == "real:-Inf"
-- select json_extract('[.5,5.,+7]','$[1]');
#guard TJ.show' (T.c "JSON_EXTRACT" #[T.t "[.5,5.,+7]", T.t "$[1]"]) == "real:5.0"
-- select json_set('[0x1F]','$[1]',2);
#guard TJ.show' (T.c "JSON_SET" #[T.t "[0x1F]", T.t "$[1]", T.i (2)]) == "text:[31,2]"
-- select json_type('[0x1F]','$[0]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "[0x1F]", T.t "$[0]"]) == "text:integer"
-- select json_type('[.5]','$[0]');
#guard TJ.show' (T.c "JSON_TYPE" #[T.t "[.5]", T.t "$[0]"]) == "text:real"
-- select json_array(json_extract('{"a":"[1]"}','$.a'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_EXTRACT" #[T.t "{\"a\":\"[1]\"}", T.t "$.a"]]) == "text:[\"[1]\"]"
-- select json_array('{"a":[1]}' ->> 'a');
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "->>" #[T.t "{\"a\":[1]}", T.t "a"]]) == "text:[\"[1]\"]"
-- select json_array('{"a":"x"}' -> 'a');
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "->" #[T.t "{\"a\":\"x\"}", T.t "a"]]) == "text:[\"x\"]"
-- select json_array(json_pretty('[1]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_PRETTY" #[T.t "[1]"]]) == "text:[\"[\\n    1\\n]\"]"
-- select json_set('{}','$.a',json_extract('{"b":[1]}','$.b'));
#guard TJ.show' (T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.c "JSON_EXTRACT" #[T.t "{\"b\":[1]}", T.t "$.b"]]) == "text:{\"a\":[1]}"
-- select json_array(json_extract('[1,2]','$[0]','$[1]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_EXTRACT" #[T.t "[1,2]", T.t "$[0]", T.t "$[1]"]]) == "text:[[1,2]]"
-- select json_array(json_extract('{"a":[1,2]}','$.a'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_EXTRACT" #[T.t "{\"a\":[1,2]}", T.t "$.a"]]) == "text:[[1,2]]"
-- select json_array('{"a":[1,2]}' ->> 'a');
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "->>" #[T.t "{\"a\":[1,2]}", T.t "a"]]) == "text:[\"[1,2]\"]"
-- select json_array('{"a":[1,2]}' -> 'a');
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "->" #[T.t "{\"a\":[1,2]}", T.t "a"]]) == "text:[[1,2]]"
-- select json_array(json_type('[1]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_TYPE" #[T.t "[1]"]]) == "text:[\"array\"]"
-- select json_array(json_quote('a'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_QUOTE" #[T.t "a"]]) == "text:[\"a\"]"
-- select json_array(json_extract('{"a":"[1]"}','$.a'),json('[2]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_EXTRACT" #[T.t "{\"a\":\"[1]\"}", T.t "$.a"], T.c "JSON" #[T.t "[2]"]]) == "text:[\"[1]\",[2]]"
-- select json_object('k',json_extract('{"a":[1]}','$.a'));
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "k", T.c "JSON_EXTRACT" #[T.t "{\"a\":[1]}", T.t "$.a"]]) == "text:{\"k\":[1]}"
-- select json_object('k','{"a":[1]}' ->> 'a');
#guard TJ.show' (T.c "JSON_OBJECT" #[T.t "k", T.c "->>" #[T.t "{\"a\":[1]}", T.t "a"]]) == "text:{\"k\":\"[1]\"}"
-- select json_quote(json_extract('{"a":[1]}','$.a'));
#guard TJ.show' (T.c "JSON_QUOTE" #[T.c "JSON_EXTRACT" #[T.t "{\"a\":[1]}", T.t "$.a"]]) == "text:[1]"
-- select json_quote('{"a":[1]}' ->> 'a');
#guard TJ.show' (T.c "JSON_QUOTE" #[T.c "->>" #[T.t "{\"a\":[1]}", T.t "a"]]) == "text:\"[1]\""
-- select json_quote(json_pretty('[1]'));
#guard TJ.show' (T.c "JSON_QUOTE" #[T.c "JSON_PRETTY" #[T.t "[1]"]]) == "text:\"[\\n    1\\n]\""
-- select json_array(json_remove('[1,2]','$[0]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_REMOVE" #[T.t "[1,2]", T.t "$[0]"]]) == "text:[[2]]"
-- select json_array(json_patch('{}','{"a":1}'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_PATCH" #[T.t "{}", T.t "{\"a\":1}"]]) == "text:[{\"a\":1}]"
-- select json_array(json_set('{}','$.a',1));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_SET" #[T.t "{}", T.t "$.a", T.i (1)]]) == "text:[{\"a\":1}]"
-- select json_array(json_array_length('[1]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_ARRAY_LENGTH" #[T.t "[1]"]]) == "text:[1]"
-- select json_array(json_valid('[1]'));
#guard TJ.show' (T.c "JSON_ARRAY" #[T.c "JSON_VALID" #[T.t "[1]"]]) == "text:[1]"

/-! json_each and json_tree: select * from json_each(json [, root]) -/

-- select * from json_each('[1,{"a":2},"x"]');
#guard TJ.rowsText (eachRows false (T.v (T.t "[1,{\"a\":2},\"x\"]")) none) == "0|1|integer|1|1||$[0]|$\x0a1|{\"a\":2}|object||3||$[1]|$\x0a2|x|text|x|8||$[2]|$"
-- select * from json_tree('{"a":[1,{"b":2}],"c d":null}');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[1,{\"b\":2}],\"c d\":null}")) none) == "|{\"a\":[1,{\"b\":2}],\"c d\":null}|object||0||$|$\x0aa|[1,{\"b\":2}]|array||2|0|$.a|$\x0a0|1|integer|1|5|2|$.a[0]|$.a\x0a1|{\"b\":2}|object||7|2|$.a[1]|$.a\x0ab|2|integer|2|8|7|$.a[1].b|$.a[1]\x0ac d||null||12|0|$.\"c d\"|$"
-- select * from json_tree('{"a":[1,{"b":2}]}','$.a');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[1,{\"b\":2}]}")) (some (T.v (T.t "$.a")))) == "a|[1,{\"b\":2}]|array||1||$.a|$\x0a0|1|integer|1|4|1|$.a[0]|$.a\x0a1|{\"b\":2}|object||6|1|$.a[1]|$.a\x0ab|2|integer|2|7|6|$.a[1].b|$.a[1]"
-- select * from json_each('5');
#guard TJ.rowsText (eachRows false (T.v (T.t "5")) none) == "|5|integer|5|0||$|$"
-- select * from json_each('{"a":[1,2]}','$.a[1]');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":[1,2]}")) (some (T.v (T.t "$.a[1]")))) == "|2|integer|2|6||$.a[1]|$.a[1]"
-- select * from json_tree('{"a":[1,2]}','$.a[1]');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[1,2]}")) (some (T.v (T.t "$.a[1]")))) == "a[1]|2|integer|2|6||$.a[1]|$"
-- select * from json_tree('{"a":{"b":{"c":1,"d":2}}}','$.a.b.d');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":{\"b\":{\"c\":1,\"d\":2}}}")) (some (T.v (T.t "$.a.b.d")))) == "a.b.d|2|integer|2|12||$.a.b.d|$"
-- select * from json_tree('[[1,2],[3,4]]','$[1][0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[[1,2],[3,4]]")) (some (T.v (T.t "$[1][0]")))) == "0|3|integer|3|7||$[1][0]|$[1]"
-- select * from json_tree('[[1,2],[3,4]]','$[1][1]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[[1,2],[3,4]]")) (some (T.v (T.t "$[1][1]")))) == "1|4|integer|4|9||$[1][1]|$"
-- select * from json_each('{"a":[1,2]}','$.a');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":[1,2]}")) (some (T.v (T.t "$.a")))) == "0|1|integer|1|4||$.a[0]|$.a\x0a1|2|integer|2|6||$.a[1]|$.a"
-- select * from json_each('{"a":[1,2]}','$.x');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":[1,2]}")) (some (T.v (T.t "$.x")))) == ""
-- select * from json_each('{"a":[1,2]}','x');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":[1,2]}")) (some (T.v (T.t "x")))) == "E:bad JSON path: 'x'"
-- select * from json_each('[1');
#guard TJ.rowsText (eachRows false (T.v (T.t "[1")) none) == "E:malformed JSON"
-- select * from json_each(NULL);
#guard TJ.rowsText (eachRows false (T.v (T.n)) none) == ""
-- select * from json_each('[]');
#guard TJ.rowsText (eachRows false (T.v (T.t "[]")) none) == ""
-- select * from json_tree('[]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[]")) none) == "|[]|array||0||$|$"
-- select * from json_tree('{}');
#guard TJ.rowsText (eachRows true (T.v (T.t "{}")) none) == "|{}|object||0||$|$"
-- select * from json_each('{}');
#guard TJ.rowsText (eachRows false (T.v (T.t "{}")) none) == ""
-- select * from json_each('{"a":1,"b":[true,false,null,1.5,"s"],"c":{"d":{}}}');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":1,\"b\":[true,false,null,1.5,\"s\"],\"c\":{\"d\":{}}}")) none) == "a|1|integer|1|2||$.a|$\x0ab|[true,false,null,1.5,\"s\"]|array||6||$.b|$\x0ac|{\"d\":{}}|object||18||$.c|$"
-- select * from json_tree('{"a":1,"b":[true,false,null,1.5,"s"],"c":{"d":{}}}');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":1,\"b\":[true,false,null,1.5,\"s\"],\"c\":{\"d\":{}}}")) none) == "|{\"a\":1,\"b\":[true,false,null,1.5,\"s\"],\"c\":{\"d\":{}}}|object||0||$|$\x0aa|1|integer|1|2|0|$.a|$\x0ab|[true,false,null,1.5,\"s\"]|array||6|0|$.b|$\x0a0|1|true|1|9|6|$.b[0]|$.b\x0a1|0|false|0|10|6|$.b[1]|$.b\x0a2||null||11|6|$.b[2]|$.b\x0a3|1.5|real|1.5|12|6|$.b[3]|$.b\x0a4|s|text|s|16|6|$.b[4]|$.b\x0ac|{\"d\":{}}|object||18|0|$.c|$\x0ad|{}|object||21|18|$.c.d|$.c"
-- select * from json_each('{"a b":1,"x_y":2,"":3,"q\"r":4,"1a":5}');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a b\":1,\"x_y\":2,\"\":3,\"q\\\"r\":4,\"1a\":5}")) none) == "a b|1|integer|1|2||$.\"a b\"|$\x0ax_y|2|integer|2|8||$.\"x_y\"|$\x0a|3|integer|3|14||$.\"\"|$\x0aq\"r|4|integer|4|17||$.\"q\\\"r\"|$\x0a1a|5|integer|5|24||$.\"1a\"|$"
-- select * from json_tree('{"a b":{"x":1},"":[1],"q\"r":{"z":0}}');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a b\":{\"x\":1},\"\":[1],\"q\\\"r\":{\"z\":0}}")) none) == "|{\"a b\":{\"x\":1},\"\":[1],\"q\\\"r\":{\"z\":0}}|object||0||$|$\x0aa b|{\"x\":1}|object||2|0|$.\"a b\"|$\x0ax|1|integer|1|7|2|$.\"a b\".x|$.\"a b\"\x0a|[1]|array||11|0|$.\"\"|$\x0a0|1|integer|1|13|11|$.\"\"[0]|$.\"\"\x0aq\"r|{\"z\":0}|object||15|0|$.\"q\\\"r\"|$\x0az|0|integer|0|21|15|$.\"q\\\"r\".z|$.\"q\\\"r\""
-- select * from json_tree('[1,[2,[3,[4]]]]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[1,[2,[3,[4]]]]")) none) == "|[1,[2,[3,[4]]]]|array||0||$|$\x0a0|1|integer|1|1|0|$[0]|$\x0a1|[2,[3,[4]]]|array||3|0|$[1]|$\x0a0|2|integer|2|4|3|$[1][0]|$[1]\x0a1|[3,[4]]|array||6|3|$[1][1]|$[1]\x0a0|3|integer|3|7|6|$[1][1][0]|$[1][1]\x0a1|[4]|array||9|6|$[1][1][1]|$[1][1]\x0a0|4|integer|4|10|9|$[1][1][1][0]|$[1][1][1]"
-- select * from json_tree('[1,[2,[3,[4]]]]','$[1][1]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[1,[2,[3,[4]]]]")) (some (T.v (T.t "$[1][1]")))) == "1|[3,[4]]|array||6||$[1][1]|$\x0a0|3|integer|3|7|6|$[1][1][0]|$[1][1]\x0a1|[4]|array||9|6|$[1][1][1]|$[1][1]\x0a0|4|integer|4|10|9|$[1][1][1][0]|$[1][1][1]"
-- select * from json_tree('{"a":[10,20]}','$.a');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[10,20]}")) (some (T.v (T.t "$.a")))) == "a|[10,20]|array||1||$.a|$\x0a0|10|integer|10|4|1|$.a[0]|$.a\x0a1|20|integer|20|7|1|$.a[1]|$.a"
-- select * from json_tree('{"a":[10,20]}','$');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[10,20]}")) (some (T.v (T.t "$")))) == "|{\"a\":[10,20]}|object||0||$|$\x0aa|[10,20]|array||1|0|$.a|$\x0a0|10|integer|10|4|1|$.a[0]|$.a\x0a1|20|integer|20|7|1|$.a[1]|$.a"
-- select * from json_each('{"a":[10,20]}','$');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":[10,20]}")) (some (T.v (T.t "$")))) == "a|[10,20]|array||1||$.a|$"
-- select * from json_each('[1,2,3]','$[#-1]');
#guard TJ.rowsText (eachRows false (T.v (T.t "[1,2,3]")) (some (T.v (T.t "$[#-1]")))) == "|3|integer|3|5||$[#-1]|$[#-1]"
-- select * from json_tree('[1,2,3]','$[#-1]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[1,2,3]")) (some (T.v (T.t "$[#-1]")))) == "0|3|integer|3|5||$[#-1]|$"
-- select * from json_tree('{"a":"long string value here that is more than eleven bytes","b":2}');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":\"long string value here that is more than eleven bytes\",\"b\":2}")) none) == "|{\"a\":\"long string value here that is more than eleven bytes\",\"b\":2}|object||0||$|$\x0aa|long string value here that is more than eleven bytes|text|long string value here that is more than eleven bytes|2|0|$.a|$\x0ab|2|integer|2|59|0|$.b|$"
-- select * from json_each('"just a string"');
#guard TJ.rowsText (eachRows false (T.v (T.t "\"just a string\"")) none) == "|just a string|text|just a string|0||$|$"
-- select * from json_tree('"just a string"');
#guard TJ.rowsText (eachRows true (T.v (T.t "\"just a string\"")) none) == "|just a string|text|just a string|0||$|$"
-- select * from json_each('{"k":[1,2]}','$.k[5]');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"k\":[1,2]}")) (some (T.v (T.t "$.k[5]")))) == ""
-- select * from json_each('[1]','$.a');
#guard TJ.rowsText (eachRows false (T.v (T.t "[1]")) (some (T.v (T.t "$.a")))) == ""
-- select * from json_each('[1]');
#guard TJ.rowsText (eachRows false (T.v (T.t "[1]")) none) == "0|1|integer|1|1||$[0]|$"
-- select * from json_each('{"a":"\u00e9\\n"}');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":\"\\u00e9\\\\n\"}")) none) == "a|é\\n|text|é\\n|2||$.a|$"
-- select * from json_tree('[1,2]','$[0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[1,2]")) (some (T.v (T.t "$[0]")))) == "0|1|integer|1|1||$[0]|$"
-- select * from json_tree('{"a":1}','$."a"');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":1}")) (some (T.v (T.t "$.\"a\"")))) == "a|1|integer|1|1||$.\"a\"|$"
-- select * from json_tree('{"a b":[1]}','$."a b"');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a b\":[1]}")) (some (T.v (T.t "$.\"a b\"")))) == "a b|[1]|array||1||$.\"a b\"|$\x0a0|1|integer|1|6|1|$.\"a b\"[0]|$.\"a b\""
-- select * from json_tree('{"a b":[1]}','$."a b"[0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a b\":[1]}")) (some (T.v (T.t "$.\"a b\"[0]")))) == "0|1|integer|1|6||$.\"a b\"[0]|$.\"a b\""
-- select * from json_each(12);
#guard TJ.rowsText (eachRows false (T.v (T.i (12))) none) == "|12|integer|12|0||$|$"
-- select * from json_each(1.5);
#guard TJ.rowsText (eachRows false (T.v (T.r (1.5))) none) == "|1.5|real|1.5|0||$|$"
-- select * from json_tree(x'0b');
#guard TJ.rowsText (eachRows true (T.v (T.b "0b")) none) == "|[]|array||0||$|$"
-- select * from json_tree(x'0c');
#guard TJ.rowsText (eachRows true (T.v (T.b "0c")) none) == "|{}|object||0||$|$"
-- select * from json_each('{a:1,b:[2]}');
#guard TJ.rowsText (eachRows false (T.v (T.t "{a:1,b:[2]}")) none) == "a|1|integer|1|1||$.a|$\x0ab|[2]|array||5||$.b|$"
-- select * from json_each('[0x1F,1,.5,2,5.,3,+7,-.5,1.e2]');
#guard TJ.rowsText (eachRows false (T.v (T.t "[0x1F,1,.5,2,5.,3,+7,-.5,1.e2]")) none) == "0|31|integer|31|2||$[0]|$\x0a1|1|integer|1|7||$[1]|$\x0a2|0.5|real|0.5|9||$[2]|$\x0a3|2|integer|2|12||$[3]|$\x0a4|5.0|real|5.0|14||$[4]|$\x0a5|3|integer|3|17||$[5]|$\x0a6|7|integer|7|19||$[6]|$\x0a7|-0.5|real|-0.5|21||$[7]|$\x0a8|100.0|real|100.0|25||$[8]|$"
-- select * from json_each('[0xffffffffffffffff]');
#guard TJ.rowsText (eachRows false (T.v (T.t "[0xffffffffffffffff]")) none) == "0|1.8446744073709552e+19|integer|1.8446744073709552e+19|2||$[0]|$"
-- select * from json_each('{"a":0x1F,"b":+5,"c":.5}');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":0x1F,\"b\":+5,\"c\":.5}")) none) == "a|31|integer|31|2||$.a|$\x0ab|5|integer|5|9||$.b|$\x0ac|0.5|real|0.5|13||$.c|$"
-- select * from json_each('[''ab'',"x\x41y",''q'']');
#guard TJ.rowsText (eachRows false (T.v (T.t "['ab',\"x\\x41y\",'q']")) none) == "0|ab|text|ab|2||$[0]|$\x0a1|xAy|text|xAy|5||$[1]|$\x0a2|q|text|q|12||$[2]|$"
-- select * from json_each('[Infinity,NaN,-Infinity,+inf]');
#guard TJ.rowsText (eachRows false (T.v (T.t "[Infinity,NaN,-Infinity,+inf]")) none) == "0|Inf|real|Inf|2||$[0]|$\x0a1||null||8||$[1]|$\x0a2|-Inf|real|-Inf|9||$[2]|$\x0a3|Inf|real|Inf|16||$[3]|$"
-- select * from json_tree('{"a":[100000,200000,300000]}','$.a[0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[100000,200000,300000]}")) (some (T.v (T.t "$.a[0]")))) == "0|100000|integer|100000|6||$.a[0]|$.a"
-- select * from json_tree('{"a":[100000,200000,300000]}','$.a[1]');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[100000,200000,300000]}")) (some (T.v (T.t "$.a[1]")))) == "a[1]|200000|integer|200000|13||$.a[1]|$"
-- select * from json_tree('{"a":1,"b":[5]}','$.b');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":1,\"b\":[5]}")) (some (T.v (T.t "$.b")))) == "b|[5]|array||5||$.b|$\x0a0|5|integer|5|8|5|$.b[0]|$.b"
-- select * from json_tree('{"a":1,"b":[5]}','$.b[0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":1,\"b\":[5]}")) (some (T.v (T.t "$.b[0]")))) == "0|5|integer|5|8||$.b[0]|$.b"
-- select * from json_tree('{"aaaaaaaaaaaaaaaaaaaaaaaaaaa":[100000,200000,300000]}','$.aaaaaaaaaaaaaaaaaaaaaaaaaaa[0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"aaaaaaaaaaaaaaaaaaaaaaaaaaa\":[100000,200000,300000]}")) (some (T.v (T.t "$.aaaaaaaaaaaaaaaaaaaaaaaaaaa[0]")))) == "0|100000|integer|100000|33||$.aaaaaaaaaaaaaaaaaaaaaaaaaaa[0]|$.aaaaaaaaaaaaaaaaaaaaaaaaaaa"
-- select * from json_tree('[[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[7]]','$[1][0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[7]]")) (some (T.v (T.t "$[1][0]")))) == "0|7|integer|7|41||$[1][0]|$[1]"
-- select * from json_tree('[[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[7]]','$[0][0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[7]]")) (some (T.v (T.t "$[0][0]")))) == "0|1|integer|1|4||$[0][0]|$[0]"
-- select * from json_tree('[[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[7]]','$[1]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[7]]")) (some (T.v (T.t "$[1]")))) == "1|[7]|array||40||$[1]|$\x0a0|7|integer|7|41|40|$[1][0]|$[1]"
-- select * from json_tree('[0x1F,[3]]','$[1]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[0x1F,[3]]")) (some (T.v (T.t "$[1]")))) == "1|[3]|array||6||$[1]|$\x0a0|3|integer|3|7|6|$[1][0]|$[1]"
-- select * from json_tree('[0x1F,[3]]','$[1][0]');
#guard TJ.rowsText (eachRows true (T.v (T.t "[0x1F,[3]]")) (some (T.v (T.t "$[1][0]")))) == "0|3|integer|3|7||$[1][0]|$[1]"
-- select * from json_each('{"a":["x","yy"],"b":{"c":[]}}','$.b');
#guard TJ.rowsText (eachRows false (T.v (T.t "{\"a\":[\"x\",\"yy\"],\"b\":{\"c\":[]}}")) (some (T.v (T.t "$.b")))) == "c|[]|array||13||$.b.c|$.b"
-- select * from json_tree('{"a":["x","yy"],"b":{"c":[]}}','$.b.c');
#guard TJ.rowsText (eachRows true (T.v (T.t "{\"a\":[\"x\",\"yy\"],\"b\":{\"c\":[]}}")) (some (T.v (T.t "$.b.c")))) == "c|[]|array||13||$.b.c|$.b"

/-! json_group_array and json_group_object: one row per list of arguments -/

-- JSON_GROUP_ARRAY over [["1"],["'a'"],["NULL"],["1.5"],["'[1]'"],["'x\"y'"]]
#guard TJ.agg "JSON_GROUP_ARRAY" #[#[T.i (1)], #[T.t "a"], #[T.n], #[T.r (1.5)], #[T.t "[1]"], #[T.t "x\"y"]] == "text:[1,\"a\",null,1.5,\"[1]\",\"x\\\"y\"]"
-- JSON_GROUP_ARRAY over []
#guard TJ.agg "JSON_GROUP_ARRAY" #[] == "text:[]"
-- JSON_GROUP_ARRAY over [["x'01'"]]
#guard TJ.agg "JSON_GROUP_ARRAY" #[#[T.b "01"]] == "text:[true]"
-- JSON_GROUP_ARRAY over [["x'0102'"]]
#guard TJ.agg "JSON_GROUP_ARRAY" #[#[T.b "0102"]] == "E:JSON cannot hold BLOB values"
-- JSON_GROUP_OBJECT over [["'a'","1"],["'b'","'x'"],["NULL","5"],["'c'","'{\"k\":1}'"],["1","2"],["'a'","NULL"]]
#guard TJ.agg "JSON_GROUP_OBJECT" #[#[T.t "a", T.i (1)], #[T.t "b", T.t "x"], #[T.n, T.i (5)], #[T.t "c", T.t "{\"k\":1}"], #[T.i (1), T.i (2)], #[T.t "a", T.n]] == "text:{\"a\":1,\"b\":\"x\",\"c\":\"{\\\"k\\\":1}\",\"1\":2,\"a\":null}"
-- JSON_GROUP_OBJECT over []
#guard TJ.agg "JSON_GROUP_OBJECT" #[] == "text:{}"
-- JSON_GROUP_OBJECT over [["NULL","1"]]
#guard TJ.agg "JSON_GROUP_OBJECT" #[#[T.n, T.i (1)]] == "text:{}"
-- JSON_GROUP_OBJECT over [["NULL","1"],["'a'","2"]]
#guard TJ.agg "JSON_GROUP_OBJECT" #[#[T.n, T.i (1)], #[T.t "a", T.i (2)]] == "text:{\"a\":2}"
-- JSON_GROUP_OBJECT over [["'a'","2"],["NULL","1"]]
#guard TJ.agg "JSON_GROUP_OBJECT" #[#[T.t "a", T.i (2)], #[T.n, T.i (1)]] == "text:{\"a\":2}"
-- JSON_GROUP_OBJECT over [["'k'","x'0102'"]]
#guard TJ.agg "JSON_GROUP_OBJECT" #[#[T.t "k", T.b "0102"]] == "E:JSON cannot hold BLOB values"
-- JSON_GROUP_ARRAY over json(...) arguments
#guard TJ.agg "JSON_GROUP_ARRAY" #[#[T.c "JSON" #[T.t "[1]"]], #[T.c "JSON" #[T.t "{\"a\":2}"]], #[T.c "JSON" #[T.t "\"s\""]]] == "text:[[1],{\"a\":2},\"s\"]"
-- JSON_GROUP_OBJECT over json(...) arguments
#guard TJ.agg "JSON_GROUP_OBJECT" #[#[T.t "a", T.c "JSON" #[T.t "[1, 2]"]], #[T.t "b", T.c "JSON" #[T.t "{\"c\" : 3}"]]] == "text:{\"a\":[1,2],\"b\":{\"c\":3}}"

/-! Small theorems -/

theorem hdrSize_small : hdrSize 11 = 1 ∧ hdrSize 12 = 2 ∧ hdrSize 256 = 3 ∧ hdrSize 65536 = 5 := by decide

theorem arityOk_json : arityOk "JSON" 1 = true ∧ arityOk "JSON" 2 = false := by decide

theorem isJsonFn_arrow : isJsonFn "->" = true ∧ isJsonFn "JSON_GROUP_ARRAY" = false := by decide

