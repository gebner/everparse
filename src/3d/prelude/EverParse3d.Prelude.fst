(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module EverParse3d.Prelude
friend EverParse3d.Kinds
module BF = LowParse.BitFields
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = LowParse.Low.Base
module LPLC = LowParse.Low.Combinators
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open LowParse.Bytes
module LS = EverParse3d.Serializer

////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////

let parser k t = LP.parser k t

let is_weaker_than #nz1 #wk1 (k:parser_kind nz1 wk1)
                   #nz2 #wk2 (k':parser_kind nz2 wk2) = k `LP.is_weaker_than` k'

let is_weaker_than_refl #nz #wk (k:parser_kind nz wk)
  : Lemma (ensures (is_weaker_than k k))
          [SMTPat (is_weaker_than k k)]
  = ()

let is_weaker_than_glb #nz1 #wk1 (k1:parser_kind nz1 wk1)
                       #nz2 #wk2 (k2:parser_kind nz2 wk2)
  : Lemma (is_weaker_than (glb k1 k2) k1 /\
           is_weaker_than (glb k1 k2) k2)
          [SMTPatOr
            [[SMTPat (is_weaker_than (glb k1 k2) k1)];
             [SMTPat (is_weaker_than (glb k1 k2) k2)]]]
  = ()

/// Parser: return
inline_for_extraction noextract
let parse_ret #t (v:t)
  : Tot (parser ret_kind t)
  = LPC.parse_ret #t v

/// Parser: bind
inline_for_extraction noextract
let parse_dep_pair p1 p2
  = LPC.parse_dtuple2 p1 p2

/// Parser: sequencing
inline_for_extraction noextract
let parse_pair p1 p2
  = LPC.nondep_then p1 p2

/// Parser: map
let injective_map a b = (a -> Tot b) //{LPC.synth_injective f}

inline_for_extraction noextract
let parse_filter p f
  = LPC.parse_filter p f

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken #nz #wk (#k:parser_kind nz wk) #t (p:parser k t)
                 #nz' #wk' (k':parser_kind nz' wk' {k' `is_weaker_than` k})
  : Tot (parser k' t)
  = LP.weaken k' p

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_left #nz #wk #k p k'
  = LP.weaken (glb k' k) p

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_right #nz #wk #k p k'
  = LP.weaken (glb k k') p

/// Parser: unreachable, for default cases of exhaustive pattern matching
inline_for_extraction noextract
let parse_impos ()
  : parser impos_kind False
  = let p : LP.bare_parser False = fun b -> None in
    LP.parser_kind_prop_equiv impos_kind p;
    p

let parse_ite e p1 p2
  = if e then p1 () else p2 ()

let nlist (n:U32.t) (t:Type) = list t

inline_for_extraction noextract
let parse_nlist n #wk #k #t p
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false #WeakKindStrongPrefix #(parse_fldata_kind (U32.v n) parse_list_kind) #(list t)
            (LowParse.Spec.FLData.parse_fldata (LowParse.Spec.List.parse_list p) (U32.v n))
            #false kind_nlist

let all_bytes = Seq.seq LP.byte
let parse_all_bytes' 
  : LP.bare_parser all_bytes 
  = fun input -> Some (input, (Seq.length input <: LP.consumed_length input))
let parse_all_bytes =
  LP.parser_kind_prop_equiv kind_all_bytes parse_all_bytes';
  parse_all_bytes'

////////////////////////////////////////////////////////////////////////////////
module B32 = FStar.Bytes
let t_at_most (n:U32.t) (t:Type) = t & all_bytes
inline_for_extraction noextract
let parse_t_at_most n #nz #wk #k #t p
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            #WeakKindStrongPrefix
            (LowParse.Spec.FLData.parse_fldata 
                (LPC.nondep_then p parse_all_bytes)
                (U32.v n))
            #false
            kind_t_at_most

////////////////////////////////////////////////////////////////////////////////
let t_exact (n:U32.t) (t:Type) = t
inline_for_extraction noextract
let parse_t_exact n #nz #wk #k #t p
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            #WeakKindStrongPrefix
            (LowParse.Spec.FLData.parse_fldata 
                p
                (U32.v n))
            #false
            kind_t_exact

////////////////////////////////////////////////////////////////////////////////
// Readers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
let reader p = LPLC.leaf_reader p

inline_for_extraction noextract
let read_filter p32 f
    = LPLC.read_filter p32 f

let read_impos : reader (parse_impos()) = 
  fun #rrel #rel sl pos -> 
    let h = FStar.HyperStack.ST.get() in
    assert (LPLC.valid (parse_impos()) h sl pos);
    LowParse.Low.Base.Spec.valid_equiv (parse_impos()) h sl pos;
    false_elim ()
  
// ////////////////////////////////////////////////////////////////////////////////
// // Validators
// ////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let validator #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator #k #t p

inline_for_extraction noextract
let validator_no_read #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator_no_read #k #t p

let parse_nlist_total_fixed_size_aux
  (n:U32.t) (#wk: _) (#k:parser_kind true wk) #t (p:parser k t)
  (x: LP.bytes)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    Seq.length x >= U32.v n
  ))
  (ensures (
    Some? (LP.parse (parse_nlist n p) x)
  ))
= let x' = Seq.slice x 0 (U32.v n) in
  let cnt = (U32.v n / k.LP.parser_kind_low) in
  FStar.Math.Lemmas.lemma_div_exact (U32.v n) k.LP.parser_kind_low;
  FStar.Math.Lemmas.nat_over_pos_is_nat (U32.v n) k.LP.parser_kind_low;
  LowParse.Spec.List.parse_list_total_constant_size p cnt x';
  LP.parser_kind_prop_equiv LowParse.Spec.List.parse_list_kind (LowParse.Spec.List.parse_list p)

let parse_nlist_total_fixed_size_kind_correct
  (n:U32.t) (#wk: _) (#k:parser_kind true wk) #t (p:parser k t)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    LP.parser_kind_prop (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)
  ))
= LP.parser_kind_prop_equiv (LowParse.Spec.FLData.parse_fldata_kind (U32.v n) LowParse.Spec.List.parse_list_kind) (parse_nlist n p);
  LP.parser_kind_prop_equiv (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p);
  Classical.forall_intro (Classical.move_requires (parse_nlist_total_fixed_size_aux n p))

inline_for_extraction noextract
let validate_nlist_total_constant_size_mod_ok (n:U32.t) #wk (#k:parser_kind true wk) (#t: Type) (p:parser k t)
  : Pure (validator_no_read (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296 /\
    U32.v n % k.LP.parser_kind_low == 0
  ))
  (ensures (fun _ -> True))
= 
      (fun #rrel #rel sl len pos ->
         let h = FStar.HyperStack.ST.get () in
         [@inline_let]
         let _ =
           parse_nlist_total_fixed_size_kind_correct n p;
           LPL.valid_facts (parse_nlist n p) h sl (LPL.uint64_to_uint32 pos);
           LPL.valid_facts (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) h sl (LPL.uint64_to_uint32 pos)
         in
         LPL.validate_total_constant_size_no_read (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) (FStar.Int.Cast.uint32_to_uint64 n) () sl len pos
      )

module LUT = LowParse.Spec.ListUpTo

inline_for_extraction
noextract
let cond_string_up_to
  (#t: eqtype)
  (terminator: t)
  (x: t)
: Tot bool
= x = terminator

let cstring
  (t: eqtype)
  (terminator: t)
: Tot Type0
= LUT.parse_list_up_to_t (cond_string_up_to terminator)

let parse_string
  #k #t p terminator
=
  LowParse.Spec.Base.parser_kind_prop_equiv k p;
  LP.weaken parse_string_kind (LUT.parse_list_up_to (cond_string_up_to terminator) p (fun _ _ _ -> ()))

inline_for_extraction noextract
let is_zero (x: FStar.UInt8.t) : Tot bool = x = 0uy

let all_zeros = list (LowParse.Spec.Combinators.parse_filter_refine is_zero)
let parse_all_zeros = LowParse.Spec.List.parse_list (LowParse.Spec.Combinators.parse_filter LowParse.Spec.Int.parse_u8 is_zero)


////////////////////////////////////////////////////////////////////////////////
// Base types
////////////////////////////////////////////////////////////////////////////////

/// UINT8
let parse____UINT8 = LowParse.Spec.Int.parse_u8
let read____UINT8 = LowParse.Low.Int.read_u8

/// UINT8BE
let parse____UINT8BE = LowParse.Spec.Int.parse_u8
let read____UINT8BE = LowParse.Low.Int.read_u8

/// UInt16BE
let parse____UINT16BE = LowParse.Spec.Int.parse_u16
let read____UINT16BE = LowParse.Low.Int.read_u16

/// UInt32BE
let parse____UINT32BE = LowParse.Spec.Int.parse_u32
let read____UINT32BE = LowParse.Low.Int.read_u32

/// UInt64BE
let parse____UINT64BE = LowParse.Spec.Int.parse_u64
let read____UINT64BE = LowParse.Low.Int.read_u64


/// UInt16
let parse____UINT16 = LowParse.Spec.BoundedInt.parse_u16_le
let read____UINT16 = LowParse.Low.BoundedInt.read_u16_le

/// UInt32
let parse____UINT32 = LowParse.Spec.BoundedInt.parse_u32_le
let read____UINT32 = LowParse.Low.BoundedInt.read_u32_le


/// UInt64
let parse____UINT64 = LowParse.Spec.Int.parse_u64_le
let read____UINT64 = LowParse.Low.Int.read_u64_le
  
inline_for_extraction noextract
let read_unit
  : LPL.leaf_reader (parse_ret ())
  = LPLC.read_ret ()

open Pulse.Lib.Core

val serializes_to #nz #wk (#k:parser_kind nz wk) #t (p:parser k t) (x:t) (b:bytes) : prop
let serializes_to p x b = LS.serializes_to p x b

let in_codomain #nz #wk (#k:parser_kind nz wk) #t (p: parser k t) (x: t) = LS.in_codomain p x
let codomain #nz #wk (#k:parser_kind nz wk) #t (p: parser k t) = LS.codomain p
let serialize #nz #wk (#k:parser_kind nz wk) #t (p: parser k t) (x: codomain p) = LS.serialize p x

let seqext1 #t (s1 s2 : Seq.seq t) :
    Lemma (requires Seq.length s1 == 1 /\ Seq.length s2 == 1 /\ Seq.index s1 0 == Seq.index s2 0)
      (ensures s1 == s2) =
  Seq.cons_head_tail s1;
  Seq.cons_head_tail s2;
  Seq.lemma_empty (Seq.tail s1);
  Seq.lemma_empty (Seq.tail s2)

let seqlem #t (s1 : Seq.seq t) (x : t) :
    Lemma (requires Seq.length s1 == 1)
      (ensures Seq.upd s1 0 x == Seq.create 1 x) =
  seqext1 (Seq.upd s1 0 x) (Seq.create 1 x)

inline_for_extraction noextract
class bv_api (t:Type0) : Type0 = {
  bv_v : t -> GTot nat;
  shift8 : i:t -> o:t { bv_v o == bv_v i / 256 };
  lsbyte : i:t -> o:UInt8.t { U8.v o == bv_v i % 256 };
}

inline_for_extraction noextract instance u8_api : bv_api U8.t = { bv_v = U8.v; shift8 = (fun x -> 0uy); lsbyte = (fun x -> x) }
inline_for_extraction noextract instance u16_api : bv_api U16.t = { bv_v = U16.v; shift8 = (fun x -> U16.div x 256us); lsbyte = Int.Cast.uint16_to_uint8 }
inline_for_extraction noextract instance u32_api : bv_api U32.t = { bv_v = U32.v; shift8 = (fun x -> U32.div x 256ul); lsbyte = Int.Cast.uint32_to_uint8 }
inline_for_extraction noextract instance u64_api : bv_api U64.t = { bv_v = U64.v; shift8 = (fun x -> U64.div x 256uL); lsbyte = Int.Cast.uint64_to_uint8 }

let pow256 (n:nat) = pow2 (8 `op_Multiply` n)

val pow256_mul (n:nat) : Lemma (pow256 (n+1) == 256 `op_Multiply` pow256 n)
let pow256_mul n =
  let k = op_Multiply 8 n in
  Math.Lemmas.pow2_double_mult k;
  Math.Lemmas.pow2_double_mult (k+1);
  Math.Lemmas.pow2_double_mult (k+2);
  Math.Lemmas.pow2_double_mult (k+3);
  Math.Lemmas.pow2_double_mult (k+4);
  Math.Lemmas.pow2_double_mult (k+5);
  Math.Lemmas.pow2_double_mult (k+6);
  Math.Lemmas.pow2_double_mult (k+7)

let write_le_lem #t (n:pos) {| bv_api t |} (x:t { bv_v x < pow256 n }) :
    Lemma (Seq.cons (lsbyte x) (pow256_mul (n-1); Endianness.n_to_le (n - 1) (bv_v (shift8 x))) == Endianness.n_to_le n (bv_v x)) =
  pow256_mul (n-1);
  let b1 = Seq.cons (lsbyte x) (Endianness.n_to_le (n - 1) (bv_v (shift8 x))) in
  let b2 = Endianness.n_to_le n (bv_v x) in
  Endianness.reveal_le_to_n b1;
  Endianness.reveal_le_to_n b2;
  Endianness.le_to_n_inj b1 b2

let le_ser_t #t (n: erased nat) (api: bv_api t) =
  (x:t { bv_v x < pow256 n }) ->
  (arr: PA.array U8.t) ->
  (i: SZ.t { SZ.v i + n <= PA.length arr }) ->
  stt SZ.t
    (exists* buf. PA.pts_to_range arr (SZ.v i) (PA.length arr) buf)
    (fun j -> pure (SZ.v j == SZ.v i + n)
      ** PA.pts_to_range arr (SZ.v i) (SZ.v j) (Endianness.n_to_le n (bv_v x))
      ** (exists* buf. PA.pts_to_range arr (SZ.v j) (PA.length arr) buf))

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn write_le_base #t (api: bv_api t) : le_ser_t #t 0 api = x arr i {
  with buf. assert (PA.pts_to_range arr (SZ.v i) (PA.length arr) buf);
  PA.pts_to_range_split arr (SZ.v i) (SZ.v i) (PA.length arr);
  FStar.Seq.Properties.slice_is_empty buf 0;
  FStar.Seq.Properties.slice_length buf;
  Seq.lemma_empty (Endianness.n_to_le 0 (bv_v x));
  i
}
```

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn write_le_step #t (#api: bv_api t) #n (ih: le_ser_t n api) : le_ser_t #t (n+1) api = x arr i {
  let i' = SZ.add i 1sz;
  PA.pts_to_range_split arr (SZ.v i) (SZ.v i') (PA.length arr);
  with buf1. assert PA.pts_to_range arr (SZ.v i) (SZ.v i') buf1;
  PA.pts_to_range_upd arr i (lsbyte x) #(SZ.v i);
  seqlem buf1 (lsbyte x);
  pow256_mul n;
  let j = ih (shift8 x) arr i';
  PA.pts_to_range_join arr (SZ.v i) (SZ.v i') (SZ.v j);
  write_le_lem (n+1) x;
  j
}
```

let write_be_lem #t (n:pos) {| bv_api t |} (x:t { bv_v x < Prims.pow2 (op_Multiply 8 n) }) :
    Lemma (Seq.snoc (pow256_mul (n-1); Endianness.n_to_be (n - 1) (bv_v (shift8 x))) (lsbyte x) == Endianness.n_to_be n (bv_v x)) =
  pow256_mul (n-1);
  let b1 = Seq.snoc (Endianness.n_to_be (n - 1) (bv_v (shift8 x))) (lsbyte x) in
  let b2 = Endianness.n_to_be n (bv_v x) in
  Endianness.reveal_be_to_n b1;
  Endianness.reveal_be_to_n b2;
  Endianness.be_to_n_inj b1 b2

let be_ser_t #t (n: erased nat) (api: bv_api t) =
  (x:t { bv_v x < pow256 n }) ->
  (arr: PA.array U8.t) ->
  (i: SZ.t { SZ.v i + n <= PA.length arr }) ->
  stt SZ.t
    (exists* buf. PA.pts_to_range arr (SZ.v i) (PA.length arr) buf)
    (fun j -> pure (SZ.v j == SZ.v i + n)
      ** PA.pts_to_range arr (SZ.v i) (SZ.v j) (Endianness.n_to_be n (bv_v x))
      ** (exists* buf. PA.pts_to_range arr (SZ.v j) (PA.length arr) buf))

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn write_be_base #t (api: bv_api t) : be_ser_t #t 0 api = x arr i {
  with buf. assert (PA.pts_to_range arr (SZ.v i) (PA.length arr) buf);
  PA.pts_to_range_split arr (SZ.v i) (SZ.v i) (PA.length arr);
  FStar.Seq.Properties.slice_is_empty buf 0;
  FStar.Seq.Properties.slice_length buf;
  Seq.lemma_empty (Endianness.n_to_be 0 (bv_v x));
  i
}
```

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn write_be_step #t (#api: bv_api t) #n (ih: be_ser_t n api) : be_ser_t #t (n+1) api = x arr i {
  pow256_mul n;
  let j = ih (shift8 x) arr i;
  let j' = SZ.add j 1sz;
  PA.pts_to_range_split arr (SZ.v j) (SZ.v j') (PA.length arr);
  with buf1. assert PA.pts_to_range arr (SZ.v j) (SZ.v j') buf1;
  PA.pts_to_range_upd arr j (lsbyte x) #(SZ.v j);
  seqlem buf1 (lsbyte x);
  PA.pts_to_range_join arr (SZ.v i) (SZ.v j) (SZ.v j');
  write_be_lem (n+1) x;
  j'
}
```

```pulse
fn pulse_ser_u8' (x: U8.t) : pulse_ser_t #true #WeakKindStrongPrefix #kind____UINT8 #U8.t parse____UINT8 (hide x) emp = arr i {
  LS.serializes_to_u8 x; 
  write_be_step (write_be_base u8_api) x arr i;
}
```

```pulse
fn pulse_ser_u16be' (x: U16.t) : pulse_ser_t #true #WeakKindStrongPrefix #kind____UINT16BE #U16.t parse____UINT16BE (hide x) emp = arr i {
  LS.serializes_to_u16be x; 
  write_be_step (write_be_step (write_be_base u16_api)) x arr i;
}
```

```pulse
fn pulse_ser_u32be' (x: U32.t) : pulse_ser_t #true #WeakKindStrongPrefix #kind____UINT32 #U32.t parse____UINT32BE (hide x) emp = arr i {
  LS.serializes_to_u32be x; 
  write_be_step (write_be_step (write_be_step (write_be_step (write_be_base u32_api)))) x arr i;
}
```

```pulse
fn pulse_ser_u64be' (x: U64.t) : pulse_ser_t #true #WeakKindStrongPrefix #kind____UINT64 #U64.t parse____UINT64BE (hide x) emp = arr i {
  LS.serializes_to_u64be x; 
  write_be_step (write_be_step (write_be_step (write_be_step (write_be_step (write_be_step (write_be_step (write_be_step (write_be_base u64_api)))))))) x arr i;
}
```

```pulse
fn pulse_ser_u16le' (x: U16.t) : pulse_ser_t #true #WeakKindStrongPrefix #kind____UINT16 #U16.t parse____UINT16 (hide x) emp = arr i {
  LS.serializes_to_u16le x;
  write_le_step (write_le_step (write_le_base u16_api)) x arr i;
}
```

```pulse
fn pulse_ser_u32le' (x: U32.t) : pulse_ser_t #true #WeakKindStrongPrefix #kind____UINT32 #U32.t parse____UINT32 (hide x) emp = arr i {
  LS.serializes_to_u32le x; 
  write_le_step (write_le_step (write_le_step (write_le_step (write_le_base u32_api)))) x arr i;
}
```

```pulse
fn pulse_ser_u64le' (x: U64.t) : pulse_ser_t #true #WeakKindStrongPrefix #kind____UINT64 #U64.t parse____UINT64 (hide x) emp = arr i {
  LS.serializes_to_u64le x; 
  write_le_step (write_le_step (write_le_step (write_le_step (write_le_step (write_le_step (write_le_step (write_le_step (write_le_base u64_api)))))))) x arr i;
}
```

let pulse_ser_u8 = pulse_ser_u8'
let pulse_ser_u8be = pulse_ser_u8
let pulse_ser_u16be = pulse_ser_u16be'
let pulse_ser_u32be = pulse_ser_u32be'
let pulse_ser_u64be = pulse_ser_u64be'
let pulse_ser_u16le = pulse_ser_u16le'
let pulse_ser_u32le = pulse_ser_u32le'
let pulse_ser_u64le = pulse_ser_u64le'

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn pulse_ser_dep_pair'
    #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: Type0) (p1: parser k1 t1)
    #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> parser k2 (t2 x))
    (x1: erased t1) (x2: erased (t2 x1))
    (frame: vprop)
    (s1: pulse_ser_t p1 (reveal x1) frame)
    (s2: pulse_ser_t (p2 x1) (reveal x2) frame)
  : pulse_ser_t #(nz1 || nz2) #wk2 #(and_then_kind k1 k2) #(dtuple2 t1 t2) (parse_dep_pair p1 p2) (| reveal x1, reveal x2 |) frame
  = arr i
{
  LS.in_codomain_dtuple2 p1 p2 x1 x2;
  LS.serializes_to_dtuple2 p1 p2 x1 x2;
  let k = s1 arr i;
  let j = s2 arr k;
  PA.pts_to_range_join arr (SZ.v i) (SZ.v k) (SZ.v j);
  j
}
```

noextract [@@noextract_to "krml"] inline_for_extraction
let pulse_ser_dep_pair
    #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: Type0) (p1: parser k1 t1)
    #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2: t1 -> Type0) (p2: (x: t1) -> parser k2 (t2 x))
    (x1: erased t1) (x2: erased (t2 x1))
    (frame: vprop)
    (s1: pulse_ser_t p1 x1 frame)
    (s2: pulse_ser_t (p2 x1) x2 frame) :
    pulse_ser_t (parse_dep_pair p1 p2) (| reveal x1, reveal x2 |) frame =
  pulse_ser_dep_pair' p1 p2 x1 x2 frame s1 s2

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn pulse_ser_pair'
    #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: Type0) (p1: parser k1 t1)
    #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2: Type0) (p2: parser k2 t2)
    (x1: erased t1) (x2: erased t2)
    (frame: vprop)
    (s1: pulse_ser_t p1 (reveal x1) frame)
    (s2: pulse_ser_t p2 (reveal x2) frame)
  : pulse_ser_t #(nz1 || nz2) #wk2 #(and_then_kind k1 k2) #(tuple2 t1 t2) (parse_pair p1 p2) (reveal x1, reveal x2) frame
  = arr i
{
  LS.in_codomain_nondep_then p1 p2 x1 x2;
  LS.serializes_to_nondep_then p1 p2 x1 x2;
  let k = s1 arr i;
  let j = s2 arr k;
  PA.pts_to_range_join arr (SZ.v i) (SZ.v k) (SZ.v j);
  j
}
```

noextract [@@noextract_to "krml"] inline_for_extraction
let pulse_ser_pair
    #nz1 (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: Type0) (p1: parser k1 t1)
    #nz2 #wk2 (#k2:parser_kind nz2 wk2) (#t2: Type0) (p2: parser k2 t2)
    (x1: erased t1) (x2: erased t2)
    (frame: vprop)
    (s1: pulse_ser_t p1 x1 frame)
    (s2: pulse_ser_t p2 x2 frame) :
    pulse_ser_t (parse_pair p1 p2) (reveal x1, reveal x2) frame =
  fun arr i ->
    pulse_ser_pair' p1 p2 x1 x2 frame s1 s2 arr i

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn pulse_ser_ret' (#t:Type0) (v:t)
  : pulse_ser_t #false #WeakKindStrongPrefix #ret_kind #t (parse_ret v) v emp
  = arr i
{
  with buf. assert (PA.pts_to_range arr (SZ.v i) (PA.length arr) buf);
  PA.pts_to_range_split arr (SZ.v i) (SZ.v i) (PA.length arr);
  Seq.Properties.slice_is_empty buf 0;
  Seq.Properties.slice_length buf;
  LS.serializes_to_ret v;
  assert pure (Seq.length (Seq.empty #U8.t) == 0);
  i
}
```

noextract [@@noextract_to "krml"] inline_for_extraction
let pulse_ser_ret (#t:Type0) (v:t) : pulse_ser_t (parse_ret v) v emp = pulse_ser_ret' v

let pulse_size_t #nz #wk #k #t (p: parser #nz #wk k t) (x: erased (codomain p)) (frame: vprop) =
  stt SZ.t frame (fun j -> frame ** pure (serialized_fits p x (SZ.v j)))

noextract [@@noextract_to "krml"] inline_for_extraction
```pulse
fn pulse_size_fixed' #nz #wk #k (#t:Type0) (p: parser #nz #wk k t) (x: erased (codomain p)) (sz: SZ.t {serialized_fits p x (SZ.v sz)})
  requires emp
  returns j:SZ.t
  ensures emp ** pure (serialized_fits p x (SZ.v j))
{
  sz
}
```

noextract [@@noextract_to "krml"] inline_for_extraction
let pulse_size_fixed #nz #wk #k #t (p: parser #nz #wk k t) (x: erased (codomain p)) (sz: SZ.t {serialized_fits p x (SZ.v sz)}) :
    pulse_size_t p x emp =
  pulse_size_fixed' p x sz

inline_for_extraction let pulse_size_u8 (x: U8.t) = LS.serializes_to_u8 x; pulse_size_fixed parse____UINT8 x 1sz
inline_for_extraction let pulse_size_u16be (x: U16.t) = LS.serializes_to_u16be x; pulse_size_fixed parse____UINT16BE x 2sz
inline_for_extraction let pulse_size_u32be (x: U32.t) = LS.serializes_to_u32be x; pulse_size_fixed parse____UINT32BE x 4sz
inline_for_extraction let pulse_size_u64be (x: U64.t) = LS.serializes_to_u64be x; pulse_size_fixed parse____UINT64BE x 8sz
inline_for_extraction let pulse_size_u16le (x: U16.t) = LS.serializes_to_u16le x; pulse_size_fixed parse____UINT16 x 2sz
inline_for_extraction let pulse_size_u32le (x: U32.t) = LS.serializes_to_u32le x; pulse_size_fixed parse____UINT32 x 4sz
inline_for_extraction let pulse_size_u64le (x: U64.t) = LS.serializes_to_u64le x; pulse_size_fixed parse____UINT64 x 8sz
