module LowParse.Steel.Leaf
include LowParse.Steel.VParse

(* Leaf readers and writers *)

module SP = Steel.FractionalPermission
module S = Steel.Memory
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module AP = LowParse.Steel.ArrayPtr

let leaf_reader
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (Type u#1)
=
  (base: Type) ->
  (src: byte_array base) ->
  SE.Steel t
    (vparse p src)
    (fun _ -> vparse p src)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (vparse p src) in
      h' (vparse p src) == s /\
      res == s.contents
    )

let exact_serializer
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (Type u#1)
=
  (base: Type0) ->
  (dst: byte_array base) ->
  (x: t) ->
  SE.Steel unit
    (AP.varrayptr dst)
    (fun _ -> AP.varrayptr dst)
    (requires (fun h ->
      AP.length (h (AP.varrayptr dst)).AP.array == Seq.length (serialize s x) /\
True //      (h (AP.varrayptr dst)).AP.perm == SP.full_perm
    ))
    (ensures (fun h _ h' ->
      let d = h (AP.varrayptr dst) in
      let d' = h' (AP.varrayptr dst) in
      d'.AP.array == d.AP.array /\
//      d'.AP.perm == d.AP.perm /\
      d'.AP.contents == serialize s x
    ))

let write_exact
  (#base: Type)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (w: exact_serializer s)
  (dst: byte_array base)
  (x: t)
: SE.Steel unit
    (AP.varrayptr dst)
    (fun _ -> vparse p dst)
    (requires (fun h ->
      AP.length (h (AP.varrayptr dst)).AP.array == Seq.length (serialize s x) /\
True //      (h (AP.varrayptr dst)).AP.perm == SP.full_perm
    ))
    (ensures (fun h _ h' ->
      let d = h (AP.varrayptr dst) in
      let d' = h' (vparse p dst) in
      array_of d' == d.AP.array /\
//      perm_of d' == SP.full_perm /\
      d'.contents == x
    ))
= w _ dst x;
  intro_vparse p dst
