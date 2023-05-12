module Test

open Steel.ST.GenElim

module A = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference

open LowParse.SteelST.Int
open LowParse.SteelST.BoundedInt
open LowParse.SteelST.VLData
open LowParse.SteelST.List

module U16 = FStar.UInt16
module U32 = FStar.UInt32

module Printf_dummy = LowStar.Printf // for dependencies only
module C = C // for dependencies only (_zero_for_deref)

#set-options "--ide_id_info_off"

let parse_bool : parser (parse_filter_kind parse_u8_kind) bool =
  parse_u8
    `parse_filter`
    (fun x -> (x = 1uy || x = 0uy))
    `parse_synth`
    (fun x -> (x = 1uy))

let serialize_bool : serializer parse_bool =
  serialize_synth
    (parse_u8 `parse_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    (serialize_u8 `serialize_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun y -> if y then 1uy else 0uy)
    ()

inline_for_extraction
noextract
let validate_bool : validator parse_bool =
  validate_synth
    (validate_filter
      validate_u8
      read_u8
      (fun x -> (x = 1uy || x = 0uy))
      (fun x -> (x = 1uy || x = 0uy))
    )
    (fun x -> (x = 1uy))
    ()

inline_for_extraction
noextract
let read_bool : leaf_reader parse_bool =
  read_synth'
    (read_filter read_u8 (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    ()

inline_for_extraction
noextract
let write_bool: exact_writer serialize_bool =
  exact_write_synth'
    (exact_write_filter
      write_u8
      (fun x -> (x = 1uy || x = 0uy))
    )
    (fun x -> (x = 1uy))
    (fun y -> if y then 1uy else 0uy)
    ()

module P = LowParse.SteelST.Fold.Print
module G = LowParse.SteelST.Fold.Gen

[@@G.specialize; noextract_to "krml"]
type scalar_t = | U8 | U32 | Bool

[@@G.specialize; noextract_to "krml"]
inline_for_extraction
let type_of_scalar (s: scalar_t) : Tot Type =
  match s with
  | U8 -> FStar.UInt8.t
  | U32 -> FStar.UInt32.t
  | Bool -> bool

[@@G.specialize; noextract_to "krml"]
let p_of_s (s: scalar_t) : G.scalar_ops (type_of_scalar s) =
  match s with
  | U8 -> {
           G.scalar_parser = weaken (G.pkind true false) parse_u8;
           G.scalar_validator = validate_weaken _ validate_u8 ();
           G.scalar_reader = read_weaken _ read_u8;
           G.scalar_jumper = jump_weaken _ jump_u8 ();
         }
  | U32 -> {
           G.scalar_parser = weaken (G.pkind true false) parse_u32;
           G.scalar_validator = validate_weaken _ validate_u32 ();
           G.scalar_reader = read_weaken _ read_u32;
           G.scalar_jumper = jump_weaken _ jump_u32 ();
         }
  | Bool -> {
           G.scalar_parser = weaken (G.pkind true false) parse_bool;
           G.scalar_validator = validate_weaken _ validate_bool ();
           G.scalar_reader = read_weaken _ read_bool;
           G.scalar_jumper = jump_weaken _ (jump_constant_size parse_bool 1sz) ();
         }

noextract
[@@G.specialize]
let test_print_u8 : G.prog type_of_scalar P.state_t P.action_t _ unit () () =
  G.PBind
    (G.PScalar () U8)
    (fun x -> G.PBind
      (G.PAction (P.PrintString "uint8:"))
      (fun _ -> G.PBind
        (G.PAction (P.PrintU8 x))
        (fun _ -> G.PAction (P.PrintString ";"))
      )
    )

noextract
[@@G.specialize]
let pchoice
  (#state_i: Type)
  (#state_t: state_i -> Type)
  (#action_t: (ret_t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (#ne #pr: bool)
  (#ttrue: G.typ type_of_scalar ne pr)
  (ptrue: G.prog type_of_scalar state_t action_t ttrue ret_t pre post)
  (#tfalse: G.typ type_of_scalar ne pr)
  (pfalse: G.prog type_of_scalar state_t action_t tfalse ret_t pre post)
: Tot (G.prog type_of_scalar state_t action_t (G.TChoice Bool (fun b -> G.TIf b (fun _ -> ttrue) (fun _ -> tfalse))) ret_t pre post)
= G.PChoice
    (fun b -> G.PIfT b (fun _ -> ptrue) (fun _ -> pfalse))

noextract
[@@G.specialize]
let test_print_choice
  (#ne #pr: bool)
  (#ttrue: G.typ type_of_scalar ne pr)
  (ptrue: G.prog type_of_scalar P.state_t P.action_t ttrue unit () ())
  (#tfalse: G.typ type_of_scalar ne pr)
  (pfalse: G.prog type_of_scalar P.state_t P.action_t tfalse unit () ())
: Tot (G.prog type_of_scalar P.state_t P.action_t (G.TChoice Bool (fun b -> G.TIf b (fun _ -> ttrue) (fun _ -> tfalse))) unit () ())
= G.PBind
    (G.PAction (P.PrintString "choice:"))
    (fun _ -> pchoice
      (G.PBind
        (G.PAction (P.PrintString "true{"))
        (fun _ -> G.PBind
          ptrue
          (fun _ -> G.PAction (P.PrintString "};"))
        )
      )
      (G.PBind
        (G.PAction (P.PrintString "false{"))
        (fun _ -> G.PBind
          pfalse
          (fun _ -> G.PAction (P.PrintString "};"))
        )
      )
    )

inline_for_extraction
noextract
let mk_size_t (sq: squash SZ.fits_u32) (x: U32.t) : Tot SZ.t = SZ.uint32_to_sizet x

noextract
[@@G.specialize]
let test_print_list
  (#t: G.typ type_of_scalar true false)
  (sq: squash SZ.fits_u32)
  (p: G.prog type_of_scalar P.state_t P.action_t t unit () ())
: Tot (G.prog type_of_scalar P.state_t P.action_t (G.TSizePrefixed U32 (mk_size_t sq) (G.TList t)) unit () ())
= G.PBind
    (G.PAction (P.PrintString "list:["))
    (fun _ -> G.PBind
      (G.PSizePrefixed U32 (mk_size_t sq) (G.PList _ p))
      (fun _ -> G.PAction (P.PrintString "];"))
    )

noextract
[@@G.specialize]
let prog_test_pretty_print (sq: squash SZ.fits_u32) : G.prog type_of_scalar P.state_t P.action_t _ unit () () =
  G.PPair
    test_print_u8
    (fun _ ->
      test_print_choice
        (test_print_list sq test_print_u8)
        test_print_u8
    )

module T = FStar.Tactics

inline_for_extraction
noextract
[@@T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
let specialize_impl_test_pretty_print0 (sq: squash SZ.fits_u32) =
  G.impl p_of_s P.a_cl P.ptr_cl (prog_test_pretty_print sq)

noextract
let typ_of_test_pretty_print (sq: squash SZ.fits_u32) =
  G.typ_of_prog (prog_test_pretty_print sq)

noextract
let type_of_test_pretty_print (sq: squash SZ.fits_u32) =
  G.type_of_typ (G.typ_of_prog (prog_test_pretty_print sq))

noextract
let parser_of_test_pretty_print (sq: squash SZ.fits_u32) : parser (G.pkind true false) (type_of_test_pretty_print sq) =
  G.parser_of_typ p_of_s (G.typ_of_prog (prog_test_pretty_print sq))

noextract
let sem_of_test_pretty_print (sq: squash SZ.fits_u32) : G.fold_t P.state_t (type_of_test_pretty_print sq) unit () () =
  G.sem P.action_sem (prog_test_pretty_print sq)

inline_for_extraction
noextract
let specialize_impl_test_pretty_print (sq: squash SZ.fits_u32) : G.fold_impl_t P.cl (parser_of_test_pretty_print sq) false (sem_of_test_pretty_print sq) =
  specialize_impl_test_pretty_print0 sq

let test_pretty_print (sq: squash SZ.fits_u32) =
  G.extract_impl_fold_no_failure
    P.no_fail
    (specialize_impl_test_pretty_print sq)
    P.mk_ll_state

[@@T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
inline_for_extraction
noextract
let validate_test_pretty_print0 (sq: squash SZ.fits_u32) =
  G.validator_of_typ p_of_s (G.typ_of_prog (prog_test_pretty_print sq))

let validate_test_pretty_print (sq: squash SZ.fits_u32) : validator (parser_of_test_pretty_print sq) =
  validate_test_pretty_print0 sq

#push-options "--z3rlimit 64"
#restart-solver

let full_test_pretty_print
  (#vb: A.v byte)
  (b: byte_array)
  (len: SZ.t)
: ST C.exit_code (A.arrayptr b vb) (fun _ -> A.arrayptr b vb)
    (A.length (A.array_of vb) == SZ.v len)
    (fun _ -> True)
= let sq = Steel.ST.Array.intro_fits_u32 () in
  with_local 0ul (fun perr ->
    let sz = validate_test_pretty_print sq b len perr in
    let _ = gen_elim () in
    let err = read_replace perr in
    if err = 0ul
    then begin
      let _ = ghost_peek_strong (parser_of_test_pretty_print sq) b in
      let _ = gen_elim () in
      let _ = test_pretty_print sq _ b () () in
      let _ = gen_elim () in
      rewrite (P.cl.ll_state_match _ _) emp;
      unpeek_strong b _ _;
      return C.EXIT_SUCCESS
    end else begin
      Steel.ST.Printf.print_string "invalid data";
      return C.EXIT_FAILURE
    end
  )

#pop-options

inline_for_extraction
noextract
let fstx
  (#a #b: Type)
  (x: (a & b))
: Tot a
= match x with
  (x1, _) -> x1

inline_for_extraction
noextract
let sndx
  (#a #b: Type)
  (x: (a & b))
: Tot b
= match x with
  (_, x2) -> x2

noextract
[@@G.specialize]
let prog_test_pretty_print_pair : G.prog type_of_scalar P.state_t P.action_t _ unit () () =
  G.PBind
    (G.PPair
      (G.PScalar _ U8)
      (fun v1 -> G.PBind
        (G.PScalar _ U8)
        (fun v2 -> G.PRet (v1, v2))
      )
    )
    (fun v ->
      let v1 = fstx v in
      let v2 = sndx v in
      G.PBind
        (G.PAction (P.PrintU8 v1))
        (fun _ -> G.PAction (P.PrintU8 v2))
    )

[@@normalize_for_extraction [delta_attr [`%G.specialize]; iota; zeta; primops]]
let test_pretty_print_pair =
  G.extract_impl_fold_no_failure
    P.no_fail
    (G.impl p_of_s P.a_cl P.ptr_cl prog_test_pretty_print_pair)
    P.mk_ll_state

module W = LowParse.SteelST.Fold.SerializationState

noextract
[@@G.specialize]
let test_write1 : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) _ unit (W.initial_index type_of_scalar) _
= G.PBind
    (G.PScalar _ U32)
    (fun v1 -> G.PBind
      (G.PAction (W.AWrite _ U32 v1))
      (fun _ -> G.PAction (W.AWeaken _ (W.index_with_trivial_postcond [W.IParse (G.TScalar U32)]) ()))
    )

// FIXME: WHY WHY WHY do I need those i0, i1, etc. annotations to typecheck this program? Without them, F* will blow up, increasing memory consumption and not returning
noextract
[@@G.specialize]
let test_write2 (sq: squash SZ.fits_u32) : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) _ unit (W.initial_index type_of_scalar) _
= let i0 = W.initial_index type_of_scalar in
  G.PPair
    (G.PScalar i0 U32)
    (fun v1 -> G.PBind
      (G.PScalar i0 U32)
      (fun v2 -> 
        let i1 = W.i_nil i0 (G.TScalar U32) in
        G.PBind
        (G.PAction (W.ANil i0 (G.TScalar U32)))
        (fun _ -> 
        let i2 = W.i_write i1 U32 v2 in
        G.PBind
          (G.PAction (W.AWrite i1 U32 v2))
          (fun _ -> 
            let i3 = W.i_cons i2 (G.TScalar U32) () in
            G.PBind
            (G.PAction (W.ACons i2 (G.TScalar U32) ()))
            (fun _ -> 
              let i4 = W.i_write i3 U32 v1 in
              G.PBind
              (G.PAction (W.AWrite i3 U32 v1))
              (fun _ -> 
                let i5 = W.i_cons i4 (G.TScalar U32) () in
                G.PBind
                (G.PAction (W.ACons i4 (G.TScalar U32) ()))
                (fun _ -> 
                  let i6 = W.i_size_prefixed i5 U32 (mk_size_t sq) (G.TList (G.TScalar U32)) () in
                  G.PBind
                  (G.PAction
                    (W.ASizePrefixed i5
                      U32 (mk_size_t sq)
                      (fun x -> x `SZ.lte` mk_size_t sq 4294967295ul)
                      (fun x -> SZ.sizet_to_uint32 x)
                      (G.TList (G.TScalar U32))
                      ()
                  ))
                  (fun _ -> G.PAction (W.AWeaken i6 (W.index_with_trivial_postcond [W.IParse (G.TSizePrefixed U32 (mk_size_t sq) (G.TList (G.TScalar U32)))]) ()))
                )
              )
            )
          )
        )
      )
    )

noextract
[@@G.specialize]
let test_write3 (sq: squash SZ.fits_u32) : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) _ unit (W.initial_index type_of_scalar) _
=
  let i0 = W.initial_index type_of_scalar in
  G.PPair
    (G.PScalar i0 U32)
    (fun v1 -> G.PBind
      (G.PScalar i0 U32)
      (fun v2 -> 
        G.pbind
        (G.PAction (W.ANil i0 (G.TScalar U32)))
        (fun (i1: W.state_i type_of_scalar) _ _ -> 
        G.pbind
          (G.PAction (W.AWrite i1 U32 v2))
          (fun (i2: W.state_i type_of_scalar) _ _ -> 
            G.pbind
            (G.PAction (W.ACons i2 (G.TScalar U32) ()))
            (fun (i3: W.state_i type_of_scalar) _ _ -> 
              G.pbind
              (G.PAction (W.AWrite i3 U32 v1))
              (fun (i4: W.state_i type_of_scalar) _ _ -> 
                G.pbind
                (G.PAction (W.ACons i4 (G.TScalar U32) ()))
                (fun (i5: W.state_i type_of_scalar) _ _ -> 
                  G.pbind
                  (G.PAction
                    (W.ASizePrefixed i5
                      U32 (mk_size_t sq)
                      (fun x -> x `SZ.lte` mk_size_t sq 4294967295ul)
                      (fun x -> SZ.sizet_to_uint32 x)
                      (G.TList (G.TScalar U32))
                      ()
                  ))
                  (fun (i6: W.state_i type_of_scalar) _ _ -> G.PAction (W.AWeaken i6 (W.index_with_trivial_postcond [W.IParse (G.TSizePrefixed U32 (mk_size_t sq) (G.TList (G.TScalar U32)))]) ()))
                )
              )
            )
          )
        )
      )
    )

[@@G.specialize]
noextract
let w_of_s
  (s: scalar_t)
: Tot (W.r_to_l_write_t (p_of_s s).scalar_parser)
= match s with
  | U8 -> coerce _ (W.r_to_l_write_rewrite (W.r_to_l_write_constant_size write_u8 1sz) (p_of_s s).scalar_parser)
  | U32 -> coerce _ (W.r_to_l_write_rewrite (W.r_to_l_write_constant_size write_u32 4sz) (p_of_s s).scalar_parser)
  | Bool -> coerce _ (W.r_to_l_write_rewrite (W.r_to_l_write_constant_size write_bool 1sz) (p_of_s s).scalar_parser)

inline_for_extraction noextract
[@@T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
let specialize_test_write3 (sq: squash SZ.fits_u32) b b_sz a =
  G.impl p_of_s (W.a_cl p_of_s w_of_s b b_sz a) (W.ptr_cl p_of_s b b_sz a) (test_write3 sq)

let extract_test_write3 (sq: squash SZ.fits_u32) vb b b_sz =
  G.extract_impl_fold_unit
    (specialize_test_write3 sq b b_sz (A.array_of vb))
    (W.mk_initial_state p_of_s vb b b_sz)

noextract
[@@G.specialize]
let tif #ne #pr = G.TIf #_ #type_of_scalar #ne #pr

noextract
[@@G.specialize]
let tchoice = G.TChoice #_ #type_of_scalar

noextract
[@@G.specialize]
let test_write4_if_true
  (sq32: squash SZ.fits_u32)
  (b: bool)
  (sq: squash (b == true))
: Tot (G.typ type_of_scalar true false)
= G.TSizePrefixed U32 (mk_size_t sq32) (G.TList (G.TScalar U8))

noextract
[@@G.specialize]
let test_write4_if_false
  (b: bool)
  (sq: squash (b == false))
: Tot (G.typ type_of_scalar true false)
= G.TScalar U8

noextract
[@@G.specialize]
let test_write4_choice_payload
  (sq32: squash SZ.fits_u32)
  (b: bool)
: Tot (G.typ type_of_scalar true false)
= tif b (test_write4_if_true sq32 b) (test_write4_if_false b)

// #push-options "--debug Test --debug_level Norm"

#push-options "--z3rlimit 16"
#restart-solver

noextract
[@@G.specialize;
  T.postprocess_with (fun _ -> T.norm [delta_attr [`%G.specialize]; iota; zeta; primops]; T.trefl())]
let test_write4 (sq: squash SZ.fits_u32) : G.prog type_of_scalar (W.state_t type_of_scalar) (W.action_t type_of_scalar) G.TUnit unit (W.initial_index type_of_scalar) _
=
  let i0 = W.initial_index type_of_scalar in
    (G.pbind
      (G.PAction (W.ANil i0 (G.TScalar U8)))
      (fun (i1: W.state_i type_of_scalar) _ _ -> G.pbind
        (G.PAction (W.AWrite i1 U8 104uy))
        (fun (i2: W.state_i type_of_scalar) _ _ -> G.pbind
          (G.PAction (W.ACons i2 (G.TScalar U8) ()))
          (fun (i3: W.state_i type_of_scalar) _ _ -> G.pbind
            (G.PAction (W.AWrite i3 U8 117uy))
            (fun (i4: W.state_i type_of_scalar) _ _ -> G.pbind
              (G.PAction (W.ACons i4 (G.TScalar U8) ()))
              (fun (i5: W.state_i type_of_scalar) _ _ -> G.pbind
                (G.PAction (W.AWrite i5 U8 98uy))
                (fun (i6: W.state_i type_of_scalar) _ _ -> G.pbind
                  (G.PAction (W.ACons i6 (G.TScalar U8) ()))
                  (fun (i7: W.state_i type_of_scalar) _ _ -> G.pbind
                    (G.PAction (W.ASizePrefixed i7
                      U32 (mk_size_t sq)
                      (fun x -> x `SZ.lte` SZ.uint32_to_sizet 4294967295ul)
                      (fun x -> SZ.sizet_to_uint32 x)
                      (G.TList (G.TScalar U8))
                      ()
                    ))
                    (fun (i8: W.state_i type_of_scalar) _ _ -> G.pbind
                      (G.PAction (W.AIf i8
                        (G.TSizePrefixed U32 (mk_size_t sq) (G.TList (G.TScalar U8)))
                        true
                        (test_write4_if_true sq true)
                        (test_write4_if_false true)
                        ()
                      ))
                      (fun (i9: W.state_i type_of_scalar) _ _ -> G.pbind
                        (G.PAction (W.AWrite i9 Bool true))
                        (fun (i10: W.state_i type_of_scalar) _ _ -> G.pbind
                          (G.PAction (
                            W.AChoice i10
                            Bool
                            (tif true
                              (test_write4_if_true sq true)
                              (test_write4_if_false true)
                            )
                            (test_write4_choice_payload sq)
                            ()
                          ))
                          (fun (i11: W.state_i type_of_scalar) _ _ -> G.pbind
                            (G.PAction (W.AWrite i11 U8 70uy))
                            (fun (i12: W.state_i type_of_scalar) _ _ -> G.pbind
                              (G.PAction (W.APair i12
                                (G.TScalar U8)
                                (tchoice Bool (test_write4_choice_payload sq))
                                ()
                              ))
                              (fun (i13: W.state_i type_of_scalar) _ _ ->
                                G.PAction (W.AWeaken i13
                                  (W.index_with_trivial_postcond [W.IParse
                                    (G.TPair
                                      (G.TScalar U8)
                                      (tchoice Bool (test_write4_choice_payload sq))
                                    )
                                  ])
                                  ()
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

#pop-options

[@@normalize_for_extraction [delta_attr [`%G.specialize]; iota; zeta; primops]]
let extract_test_write4 (sq: squash SZ.fits_u32) vb b b_sz =
  G.extract_impl_fold_unit
    (G.impl p_of_s (W.a_cl p_of_s w_of_s b b_sz (A.array_of vb)) (W.ptr_cl p_of_s b b_sz (A.array_of vb)) (test_write4 sq))
    (W.mk_initial_state p_of_s vb b b_sz)
