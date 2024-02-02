module EverParse3d.Serializer
open LowParse.Bytes
open LowParse.Spec.Base
open LowParse.Spec.Combinators

let in_codomain p x = exists y. p y == Some (x, Seq.length y)

let serialize p x = IndefiniteDescription.indefinite_description_ghost bytes (fun y -> p y == Some (x, Seq.length y))

let serializes_to_iff p x b =
  introduce p b == Some (x, Seq.length b) ==> serializes_to p x b with _.
    LowParse.Spec.Base.parse_injective p (serialize p x) b

let serialize_inj p x1 x2 = ()

let serializes_to_ret v = ()

let serializes_to_filter p f x = parse_filter_eq p f (serialize p x)

let in_codomain_filter p f x =
  introduce in_codomain (parse_filter p f) x ==> in_codomain p x with _.
    parse_filter_eq p f (serialize (parse_filter p f) x);
  introduce in_codomain p x ==> in_codomain (parse_filter p f) x with _. serializes_to_filter p f x

let serializes_to_dtuple2 p1 p2 x1 x2 =
  let b1 = serialize p1 x1 in
  let b2 = serialize (p2 x1) x2 in
  LowParse.Spec.Base.parse_strong_prefix p1 b1 (Seq.append b1 b2);
  LowParse.Spec.Combinators.parse_dtuple2_eq p1 p2 (Seq.append b1 b2);
  Seq.append_slices b1 b2

let in_codomain_dtuple2 p1 p2 x1 x2 =
  introduce in_codomain p1 x1 /\ in_codomain (p2 x1) x2 ==> in_codomain (parse_dtuple2 p1 p2) (| x1, x2 |) with _. serializes_to_dtuple2 p1 p2 x1 x2;
  introduce in_codomain (parse_dtuple2 p1 p2) (|x1, x2|) ==> in_codomain p1 x1 /\ in_codomain (p2 x1) x2 with _. begin
    let b = serialize (parse_dtuple2 p1 p2) (| x1, x2 |) in
    LowParse.Spec.Combinators.parse_dtuple2_eq p1 p2 b;
    let Some (x1', c1) = p1 b in
    let b1 = Seq.slice b 0 c1 in
    LowParse.Spec.Base.parse_strong_prefix p1 b b1
  end

let serializes_to_nondep_then p1 p2 x1 x2 =
  let b1 = serialize p1 x1 in
  let b2 = serialize p2 x2 in
  LowParse.Spec.Base.parse_strong_prefix p1 b1 (Seq.append b1 b2);
  LowParse.Spec.Combinators.nondep_then_eq p1 p2 (Seq.append b1 b2);
  Seq.append_slices b1 b2

let in_codomain_nondep_then p1 p2 x1 x2 =
  introduce in_codomain p1 x1 /\ in_codomain p2 x2 ==> in_codomain (nondep_then p1 p2) (x1, x2) with _. serializes_to_nondep_then p1 p2 x1 x2;
  introduce in_codomain (nondep_then p1 p2) (x1, x2) ==> in_codomain p1 x1 /\ in_codomain p2 x2 with _. begin
    let b = serialize (nondep_then p1 p2) (x1, x2) in
    LowParse.Spec.Combinators.nondep_then_eq p1 p2 b;
    let Some (x1', c1) = p1 b in
    let b1 = Seq.slice b 0 c1 in
    LowParse.Spec.Base.parse_strong_prefix p1 b b1
  end

let serializes_to_u8 x =
  LowParse.Spec.Int.parse_u8_spec (Endianness.n_to_be 1 (UInt8.v x))

let serializes_to_u16be x =
  LowParse.Spec.Int.parse_u16_spec (Endianness.n_to_be 2 (UInt16.v x))

let serializes_to_u32be x =
  LowParse.Spec.Int.parse_u32_spec (Endianness.n_to_be 4 (UInt32.v x))

let serializes_to_u64be x =
  LowParse.Spec.Int.parse_u64_spec (Endianness.n_to_be 8 (UInt64.v x))

let serializes_to_u16le x =
  LowParse.Spec.BoundedInt.parse_u16_le_spec (Endianness.n_to_le 2 (UInt16.v x))

let serializes_to_u32le x =
  LowParse.Spec.BoundedInt.parse_u32_le_spec (Endianness.n_to_le 4 (UInt32.v x))

let serializes_to_u64le x =
  LowParse.Spec.Int.parse_u64_le_spec (Endianness.n_to_le 8 (UInt64.v x))

let serializes_to_fldata p sz x = ()

let in_codomain_fldata p sz x =
  introduce in_codomain (parse_fldata p sz) x ==> in_codomain p x /\ Seq.length (serialize p x) == sz with _.
    serializes_to_iff p x (serialize (parse_fldata p sz) x);
  introduce in_codomain p x /\ Seq.length (serialize p x) == sz ==> in_codomain (parse_fldata p sz) x with _.
    serializes_to_fldata p sz x

let serializes_to_list_nil p = parse_list_eq p Seq.empty

let serializes_to_list_cons p x xs =
  let b1 = serialize p x in
  let b2 = serialize (parse_list p) xs in
  let bs = Seq.append b1 b2 in
  LowParse.Spec.Base.parse_strong_prefix p b1 bs;
  parse_list_eq p bs;
  Seq.append_slices b1 b2

let in_codomain_list_cons p x xs =
  introduce in_codomain (parse_list p) (x::xs) ==>
      in_codomain p x /\ Seq.length (serialize p x) > 0 /\ in_codomain (parse_list p) xs with _.
  begin
    let bs = serialize (parse_list p) (x::xs) in
    parse_list_eq p bs;
    let Some (x', n) = p bs in
    LowParse.Spec.Base.parse_strong_prefix p bs (Seq.slice bs 0 n);
    serializes_to_iff p x (Seq.slice bs 0 n)
  end;
  introduce in_codomain p x /\ Seq.length (serialize p x) > 0 /\ in_codomain (parse_list p) xs ==>
      in_codomain (parse_list p) (x::xs) with _.
    serializes_to_list_cons p x xs
