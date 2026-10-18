import LeanItsdangerous
import LeanJson

/-!
# `Codec Json`: lean-json as the payload format

Helper for the examples (not itself a port). Upstream's serializers default
to Python's `json` module, in two styles, and this gives `Json` both:

* `Serializer` / `TimedSerializer`: `json.dumps(obj)`, with separators
  `", "` and `": "` and `ensure_ascii=True` (`[1, 2, 3, 4]`).
* `URLSafeSerializer` / `URLSafeTimedSerializer`: `_CompactJSON`, with
  separators `","` and `":"` and `ensure_ascii=False` (`[1,2,3,4]`): lean-json's
  own compact printer.

Each constructor picks its style by itself (`Codec` vs `CompactCodec`), as
upstream's do, so `s.dumps (json% [1, 2, 3, 4])` gives upstream's token.
Decoding is lean-json's parser either way.
-/

open LeanItsdangerous LeanJson

namespace ItsdangerousJson

/-- One scalar (or object key) as lean-json prints it. -/
def scalar (ensureAscii : Bool) (v : Json) : String :=
  (String.fromUTF8? (print v { ensureAscii }).val).getD ""

mutual
/-- `json.dumps(obj)` with Python's default separators and `ensure_ascii`. -/
def pyDumps : Json → String
  | .arr xs => "[" ++ pyElems xs ++ "]"
  | .obj fs => "{" ++ pyFields fs ++ "}"
  | v => scalar true v
/-- Array elements, separated by `", "`. -/
def pyElems : List Json → String
  | [] => ""
  | [x] => pyDumps x
  | x :: xs => pyDumps x ++ ", " ++ pyElems xs
/-- Object members, `"key": value`, separated by `", "`. -/
def pyFields : List (String × Json) → String
  | [] => ""
  | [(k, v)] => scalar true (.str k) ++ ": " ++ pyDumps v
  | (k, v) :: fs => scalar true (.str k) ++ ": " ++ pyDumps v ++ ", " ++ pyFields fs
end

/-- `json.loads`. -/
def loads (b : Bytes) : Except String Json :=
  match from_json (ByteArray.mk b.toArray) with
  | .ok v => .ok v.val
  | .error e => .error e.description

/-- The plain serializers' payload: `json.dumps`. A default instance above
the library's `String` one: with this module imported, `Serializer.new
"secret-key"` is a JSON serializer, as upstream's is. -/
@[default_instance high] instance jsonCodec : LeanItsdangerous.Codec Json := ⟨fun v => Bytes.ofString (pyDumps v), loads⟩

/-- The URL-safe serializers' payload: `_CompactJSON`. -/
@[default_instance high] instance compactJsonCodec : LeanItsdangerous.CompactCodec Json := ⟨⟨fun v => (print v).val.toList, loads⟩⟩

end ItsdangerousJson
