module EverParse3d.Serializer
open LowParse.Bytes
open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.FLData
open LowParse.Spec.List

val in_codomain #k #t (p: parser k t) (x: t) : prop

let codomain #k #t (p: parser k t) : Type =
  x:t { in_codomain p x }

val serialize #k #t (p: parser k t) (x: codomain p) : GTot (b:bytes { p b == Some (x, Seq.length b) })

let serializes_to #k #t (p: parser k t) (x: t) (y: bytes) : prop =
  in_codomain p x /\ serialize p x == y

val serializes_to_intro #k #t (p: parser k t) (x: t) (b: bytes) :
    Lemma (requires p b == Some (x, Seq.length b)) (ensures serializes_to p x b)

val serialize_inj #k #t (p: parser k t) (x1 x2: codomain p) :
    Lemma (requires serialize p x1 == serialize p x2) (ensures x1 == x2)

val serializes_to_ret #t (v: t) : Lemma (serializes_to (parse_ret v) v Seq.empty)

val serializes_to_filter #k #t (p: parser k t) (f: t -> bool) (x: t {f x}) :
  Lemma (requires in_codomain p x) (ensures serializes_to (parse_filter p f) x (serialize p x))
val in_codomain_filter #k #t (p: parser k t) (f: t -> bool) (x: t {f x}) :
  Lemma (in_codomain (parse_filter p f) x <==> in_codomain p x)

val serializes_to_dtuple2 #k1 #t1 (p1: parser k1 t1 {is_strong p1}) #k2 (#t2: t1 -> Type) (p2: (x: t1 -> parser k2 (t2 x))) (x1: t1) (x2 : t2 x1) :
    Lemma (requires in_codomain p1 x1 /\ in_codomain (p2 x1) x2)
        (ensures serializes_to (parse_dtuple2 p1 p2) (| x1, x2 |) (Seq.append (serialize p1 x1) (serialize (p2 _) x2)))
val in_codomain_dtuple2 #k1 #t1 (p1: parser k1 t1 {is_strong p1}) #k2 (#t2: t1 -> Type) (p2: (x: t1 -> parser k2 (t2 x))) (x1: t1) (x2 : t2 x1) :
    Lemma (in_codomain (parse_dtuple2 p1 p2) (| x1, x2 |) <==> (in_codomain p1 x1 /\ in_codomain (p2 x1) x2))

val serializes_to_nondep_then #k1 #t1 (p1:parser k1 t1 {is_strong p1}) #k2 #t2 (p2:parser k2 t2) (x1 : t1) (x2 : t2) :
    Lemma (requires in_codomain p1 x1 /\ in_codomain p2 x2)
        (ensures serializes_to (nondep_then p1 p2) (x1, x2) (Seq.append (serialize p1 x1) (serialize p2 x2)))
val in_codomain_nondep_then #k1 #t1 (p1:parser k1 t1 {is_strong p1}) #k2 #t2 (p2:parser k2 t2) (x1 : t1) (x2 : t2) :
    Lemma (in_codomain (nondep_then p1 p2) (x1, x2) <==> in_codomain p1 x1 /\ in_codomain p2 x2)

val serializes_to_u8 x : Lemma (serializes_to LowParse.Spec.Int.parse_u8 x (Endianness.n_to_be 1 (UInt8.v x)))
val serializes_to_u16be x : Lemma (serializes_to LowParse.Spec.Int.parse_u16 x (Endianness.n_to_be 2 (UInt16.v x)))
val serializes_to_u32be x : Lemma (serializes_to LowParse.Spec.Int.parse_u32 x (Endianness.n_to_be 4 (UInt32.v x)))
val serializes_to_u64be x : Lemma (serializes_to LowParse.Spec.Int.parse_u64 x (Endianness.n_to_be 8 (UInt64.v x)))
val serializes_to_u16le x : Lemma (serializes_to LowParse.Spec.BoundedInt.parse_u16_le x (Endianness.n_to_le 2 (UInt16.v x)))
val serializes_to_u32le x : Lemma (serializes_to LowParse.Spec.BoundedInt.parse_u32_le x (Endianness.n_to_le 4 (UInt32.v x)))
val serializes_to_u64le x : Lemma (serializes_to LowParse.Spec.Int.parse_u64_le x (Endianness.n_to_le 8 (UInt64.v x)))

val serializes_to_fldata #k #t (p: parser k t) sz x :
  Lemma (requires in_codomain p x /\ Seq.length (serialize p x) == sz)
    (ensures serializes_to (parse_fldata p sz) x (serialize p x))
val in_codomain_fldata #k #t (p: parser k t) sz x :
  Lemma (in_codomain (parse_fldata p sz) x <==> in_codomain p x /\ Seq.length (serialize p x) == sz)

val serializes_to_list_nil #k #t (p: parser k t) :
  Lemma (serializes_to (parse_list p) [] Seq.empty)
val serializes_to_list_cons #k #t (p: parser k t {is_strong p}) x xs :
  Lemma
    (requires in_codomain p x /\ Seq.length (serialize p x) > 0 /\ in_codomain (parse_list p) xs)
    (ensures serializes_to (parse_list p) (x::xs) (Seq.append (serialize p x) (serialize (parse_list p) xs)))
val in_codomain_list_cons #k #t (p: parser k t {is_strong p}) x xs :
  Lemma (in_codomain (parse_list p) (x::xs) <==>
    in_codomain p x /\ Seq.length (serialize p x) > 0 /\ in_codomain (parse_list p) xs)