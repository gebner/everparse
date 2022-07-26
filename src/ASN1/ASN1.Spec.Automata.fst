module ASN1.Spec.Automata

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open ASN1.Base

noeq
type automata_control_param = {
  control_t : eqtype;
  ch_t : eqtype;
  fail_check : control_t -> ch_t -> bool;
  termination_check : (s : control_t) -> 
                      (ch : ch_t {fail_check s ch = false}) -> bool;
  next_state : (s : control_t) ->
               (ch : ch_t {fail_check s ch = false /\ termination_check s ch = false}) -> control_t;
}

(*

type extend_control_t (t : Type) =
| CFail 
| CTerm 
| CCont : (s : t) -> extend_control_t t

let automata_cp_small_step 
  (cp : automata_control_param)
  (s : cp.control_t)
  (ch : cp.ch_t)
: extend_control_t (cp.control_t)
= if (cp.fail_check s ch) then
    CFail
  else 
    if (cp.termination_check s ch) then
      CTerm
    else
      CCont (cp.next_state s ch)

// Cannot define big step due to non-termination unless finite input

let rec automata_cp_big_step_list
  (cp : automata_control_param)
  (s : cp.control_t)
  (lch : list cp.ch_t)
: Tot (extend_control_t cp.control_t)
  (decreases lch)
= let cur = automata_cp_small_step cp s in
  match lch with
  | [] -> CFail
  | ch :: tl ->
    match (cur ch) with
    | CCont s' -> automata_cp_big_step_list cp s' tl
    | other -> other

*)

noeq
type automata_data_param (cp : automata_control_param) = {
  ret_t : eqtype;
  partial_t : eqtype;
  pre_t : cp.control_t -> partial_t -> Type0;
  post_t : (s : cp.control_t) -> 
           (data : partial_t {pre_t s data}) ->
           ret_t -> Type0;
  update_term : (s : cp.control_t) ->
                (data : partial_t {pre_t s data}) ->
                (ch : cp.ch_t {cp.fail_check s ch = false /\ cp.termination_check s ch = true}) ->
                (ret : ret_t {post_t s data ret});
  update_next : (s : cp.control_t) ->
                (data : partial_t {pre_t s data}) ->
                (ch : cp.ch_t {cp.fail_check s ch = false /\ cp.termination_check s ch = false}) ->
                (data' : partial_t {pre_t (cp.next_state s ch) data'});
  lemma_cast_ret : (state : cp.control_t) ->
                   (data : partial_t {pre_t state data}) ->
                   (ch : cp.ch_t {cp.fail_check state ch = false /\ cp.termination_check state ch = false}) ->
                   (ret : ret_t) ->
                   (post_t (cp.next_state state ch) (update_next state data ch) ret ==> post_t state data ret)
}

(*
type extend_control_data_t
  (cp : automata_control_param)
  (dp : automata_data_param cp)
= | DFail
  | DTerm : dp.ret_t -> extend_control_data_t cp dp
  | DCont : (s : cp.control_t) -> (data : dp.partial_t {dp.pre_t s data}) -> extend_control_data_t cp dp

let automata_cp_dp_small_step
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (ch : cp.ch_t)
: extend_control_data_t cp dp
= if cp.fail_check s ch then
    DFail
  else
    if cp.termination_check s ch then
      DTerm (dp.update_term s data ch)
    else 
      DCont (cp.next_state s ch) (dp.update_next s data ch)
*)     

noeq
type automata_bare_parser_param (cp : automata_control_param) = {
  ch_t_bare_parser : bare_parser cp.ch_t;
  ch_t_bare_parser_valid : ((b : bytes) ->
    Lemma (match (parse ch_t_bare_parser b) with
                    | Some (_, n) -> n > 0
                    | None -> True))
}

let id_cast
  (t : eqtype)
  (p1 : t -> Type0)
  (p2 : t -> Type0)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (x : t {p1 x})
: (x' : t {p2 x'})
= let _ = lem x in
  (x <: (x : t {p2 x}))

let rec automata_bare_parser'
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (b : bytes)
: Tot (option ((ret : dp.ret_t {dp.post_t s data ret}) * (consumed_length b)))
  (decreases (Seq.length b))
= match (parse bp.ch_t_bare_parser b) with
  | None -> None
  | Some (ch, l) ->
    if cp.fail_check s ch then
      None
    else
      if cp.termination_check s ch then
        Some (dp.update_term s data ch, l)
      else
        (
        let s' = cp.next_state s ch in
        let data' = dp.update_next s data ch in
        let _ = bp.ch_t_bare_parser_valid b in
        let (b' : bytes{Seq.length b' < Seq.length b}) = Seq.slice b l (Seq.length b) in
        match (automata_bare_parser' cp dp bp s' data' b') with
        | None -> None
        | Some (ret, l') ->
          Some (id_cast dp.ret_t (dp.post_t s' data') (dp.post_t s data) (dp.lemma_cast_ret s data ch) ret, l + l')
        )

type automata_default_parser_kind : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
}

noeq
type automata_parser_param (cp : automata_control_param) (dp : automata_data_param cp) (bp : automata_bare_parser_param cp) = {
  ch_t_parser_valid : unit -> Lemma (parser_kind_prop automata_default_parser_kind bp.ch_t_bare_parser);

  lemma_update_term_inj2 : ((state : cp.control_t) -> 
    (data1 : dp.partial_t {dp.pre_t state data1}) ->
    (data2 : dp.partial_t {dp.pre_t state data2}) ->
    (ch1 : cp.ch_t {cp.fail_check state ch1 = false /\ cp.termination_check state ch1 = true}) ->
    (ch2 : cp.ch_t {cp.fail_check state ch2 = false /\ cp.termination_check state ch2 = true}) ->
    Lemma (requires (dp.update_term state data1 ch1 = dp.update_term state data2 ch2))
          (ensures (data1 = data2 /\ ch1 = ch2)));

  lemma_update_term_next_non_intersect : ((state : cp.control_t) ->
    (data1 : dp.partial_t {dp.pre_t state data1}) ->
    (data2 : dp.partial_t {dp.pre_t state data2}) ->
    (ch1 : cp.ch_t {cp.fail_check state ch1 = false /\ cp.termination_check state ch1 = true}) ->
    (ch2 : cp.ch_t {cp.fail_check state ch2 = false /\ cp.termination_check state ch2 = false}) ->
    (ret1 : dp.ret_t {dp.post_t state data1 ret1}) ->
    (ret2 : dp.ret_t {dp.post_t (cp.next_state state ch2) (dp.update_next state data2 ch2) ret2}) ->
    Lemma (requires (ret1 = dp.update_term state data1 ch1 /\ ret1 = ret2))
          (ensures False));

  lemma_update_next_non_intersect : ((state : cp.control_t) ->
    (data1 : dp.partial_t {dp.pre_t state data1}) ->
    (data2 : dp.partial_t {dp.pre_t state data2}) ->
    (ch1 : cp.ch_t {cp.fail_check state ch1 = false /\ cp.termination_check state ch1 = false}) ->
    (ch2 : cp.ch_t {cp.fail_check state ch2 = false /\ cp.termination_check state ch2 = false}) ->
    (ret1 : dp.ret_t {dp.post_t (cp.next_state state ch1) (dp.update_next state data1 ch1) ret1}) ->
    (ret2 : dp.ret_t {dp.post_t (cp.next_state state ch2) (dp.update_next state data2 ch2) ret2}) ->
    Lemma (requires (cp.next_state state ch1 <> cp.next_state state ch2 /\ ret1 = ret2))
          (ensures False));

  lemma_update_next_inj2 : ((state : cp.control_t) -> 
    (data1 : dp.partial_t {dp.pre_t state data1}) ->
    (data2 : dp.partial_t {dp.pre_t state data2}) ->
    (ch1 : cp.ch_t {cp.fail_check state ch1 = false /\ cp.termination_check state ch1 = false}) ->
    (ch2 : cp.ch_t {cp.fail_check state ch2 = false /\ cp.termination_check state ch2 = false}) ->
    Lemma (requires cp.next_state state ch1 = cp.next_state state ch2 /\ dp.update_next state data1 ch1 = dp.update_next state data2 ch2)
          (ensures data1 = data2 /\ ch1 = ch2))
}

let and_then_cases_injective_dep_precond
  (#t:Type)
  (#t': Type)
  (gt : t -> t' -> Type0)
  (p': ((x : t) -> Tot (bare_parser (y : t' {gt x y}))))
  (x1 x2: t)
  (b1 b2: bytes)
: GTot Type0
= Some? (parse (p' x1) b1) /\
  Some? (parse (p' x2) b2) /\ (
    let (Some (v1, _)) = parse (p' x1) b1 in
    let (Some (v2, _)) = parse (p' x2) b2 in
    v1 == v2
  )

let and_then_cases_injective_dep
  (#t : Type)
  (#t' : Type)
  (gt : t -> t' -> Type0)
  (p': ((m : t) -> Tot (bare_parser (x : t' {gt m x}))))
: GTot Type0
= forall (x1 x2: t) (b1 b2: bytes) . {:pattern (parse (p' x1) b1); (parse (p' x2) b2)}
  and_then_cases_injective_dep_precond gt p' x1 x2 b1 b2 ==>
  x1 == x2

let and_then_cases_injective_dep_intro
  (#t : Type)
  (#t': Type)
  (gt : t -> t' -> Type0)
  (p': ((x : t) -> Tot (bare_parser (y : t' {gt x y}))))
  (lem: (
    (x1: t) -> 
    (x2: t) ->
    (b1: bytes) ->
    (b2: bytes) ->
    Lemma
    (requires (and_then_cases_injective_dep_precond gt p' x1 x2 b1 b2))
    (ensures (x1 == x2))
  ))
: Lemma
  (and_then_cases_injective_dep gt p')
= Classical.forall_intro_4 (fun x1 x2 b1 b2 -> (Classical.move_requires (lem x1 x2 b1) b2))

let rec automata_bare_parser'_pf1_aux
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
  (x1 : dp.partial_t {dp.pre_t s x1})
  (x2 : dp.partial_t {dp.pre_t s x2})
  (b1 : bytes)
  (b2 : bytes)
: Lemma 
  (requires (and_then_cases_injective_dep_precond (dp.post_t s) (automata_bare_parser' cp dp bp s) x1 x2 b1 b2))
  (ensures (x1 == x2))
  (decreases (Seq.length b1))
= let p = automata_bare_parser' cp dp bp in
  match (parse (p s x1) b1) with | Some (ret1, l1) ->
  match (parse (p s x2) b2) with | Some (ret2, l2) ->
  match (parse (bp.ch_t_bare_parser) b1) with | Some (ch1, l01) ->
  match (parse (bp.ch_t_bare_parser) b2) with | Some (ch2, l02) ->
  if cp.fail_check s ch1 then
    _
  else if cp.fail_check s ch2 then
    _
  else if cp.termination_check s ch1 then
  (
    if cp.termination_check s ch2 then
      pp.lemma_update_term_inj2 s x1 x2 ch1 ch2 
    else
      pp.lemma_update_term_next_non_intersect s x1 x2 ch1 ch2 ret1 ret2
  )
  else
  (
    if cp.termination_check s ch2 then
      pp.lemma_update_term_next_non_intersect s x2 x1 ch2 ch1 ret2 ret1
    else
    (
      let s'1 = cp.next_state s ch1 in
      let s'2 = cp.next_state s ch2 in
      let x'1 = dp.update_next s x1 ch1 in
      let _ = bp.ch_t_bare_parser_valid b1 in
      let (b'1 : bytes{Seq.length b'1 < Seq.length b1}) = Seq.slice b1 l01 (Seq.length b1) in
      let x'2 = dp.update_next s x2 ch2 in
      let _ = bp.ch_t_bare_parser_valid b2 in
      let (b'2 : bytes{Seq.length b'2 < Seq.length b2}) = Seq.slice b2 l02 (Seq.length b2) in
      if s'1 = s'2 then
      (
        let _ = automata_bare_parser'_pf1_aux cp dp bp pp s'1 x'1 x'2 b'1 b'2 in
        pp.lemma_update_next_inj2 s x1 x2 ch1 ch2
      )
      else
      (
        pp.lemma_update_next_non_intersect s x1 x2 ch1 ch2 ret1 ret2
      )
    )
  )      

let automata_bare_parser'_pf1
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
: Lemma (and_then_cases_injective_dep (dp.post_t s) (automata_bare_parser' cp dp bp s))
= let p = automata_bare_parser' cp dp bp s in
  and_then_cases_injective_dep_intro (dp.post_t s) p (automata_bare_parser'_pf1_aux cp dp bp pp s)

let rec automata_bare_parser'_pf2_aux
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
  (x : dp.partial_t {dp.pre_t s x})
  (b1 : bytes)
  (b2 : bytes)
: Lemma (requires no_lookahead_on_precond (automata_bare_parser' cp dp bp s x) b1 b2)
        (ensures no_lookahead_on_postcond (automata_bare_parser' cp dp bp s x) b1 b2)
        (decreases (Seq.length b1))
= let p = automata_bare_parser' cp dp bp s x in
  let _ = pp.ch_t_parser_valid () in
  let _ = parser_kind_prop_equiv automata_default_parser_kind bp.ch_t_bare_parser in
  match (parse p b1) with | Some (ret1, l1) ->
  match (parse (bp.ch_t_bare_parser) b1) with | Some (ch1, l01) ->
  let _ = 
    Seq.lemma_split (Seq.slice b2 0 l1) l01;
    Seq.lemma_split (Seq.slice b1 0 l1) l01
  in
  assert (Seq.slice b2 0 l01 == Seq.slice b1 0 l01);
  match (parse (bp.ch_t_bare_parser) b2) with 
  | None -> 
    assert (no_lookahead_on bp.ch_t_bare_parser b1 b2)
  | Some (ch2, l02) ->
    assert (ch1 = ch2);
    assert (injective_precond bp.ch_t_bare_parser b1 b2);
    assert ((l01 <: nat) = (l02 <: nat));
    if cp.fail_check s ch1 then
      _
    else if cp.termination_check s ch1 then
      _
    else
    (
      let s' = cp.next_state s ch1 in
      let x' = dp.update_next s x ch1 in
      let _ = bp.ch_t_bare_parser_valid b1 in
      let (b'1 : bytes{Seq.length b'1 < Seq.length b1}) = Seq.slice b1 l01 (Seq.length b1) in
      let _ = bp.ch_t_bare_parser_valid b2 in
      let (b'2 : bytes{Seq.length b'2 < Seq.length b2}) = Seq.slice b2 l01 (Seq.length b2) in
      automata_bare_parser'_pf2_aux cp dp bp pp s' x' b'1 b'2
    )

let automata_bare_parser'_pf2
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
  (x : dp.partial_t {dp.pre_t s x})
: Lemma (no_lookahead (automata_bare_parser' cp dp bp s x))
= Classical.forall_intro_2 (fun b1 b2 -> Classical.move_requires (automata_bare_parser'_pf2_aux cp dp bp pp s x b1) b2)

let rec automata_bare_parser'_pf3_aux
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
  (x : dp.partial_t {dp.pre_t s x})
  (b1 : bytes)
  (b2 : bytes)
: Lemma (requires injective_precond (automata_bare_parser' cp dp bp s x) b1 b2)
        (ensures injective_postcond (automata_bare_parser' cp dp bp s x) b1 b2)
        (decreases (Seq.length b1))
= let p = automata_bare_parser' cp dp bp s x in
  let _ = pp.ch_t_parser_valid () in
  let _ = parser_kind_prop_equiv automata_default_parser_kind bp.ch_t_bare_parser in
  match (parse p b1) with | Some (ret1, l1) ->
  match (parse p b2) with | Some (ret2, l2) ->
  match (parse (bp.ch_t_bare_parser) b1) with | Some (ch1, l01) ->
  match (parse (bp.ch_t_bare_parser) b2) with | Some (ch2, l02) ->
  let _ = 
    Seq.lemma_split (Seq.slice b1 0 l1) l01;
    Seq.lemma_split (Seq.slice b2 0 l2) l02
  in
  if cp.fail_check s ch1 then
    _
  else if cp.fail_check s ch2 then
    _
  else if cp.termination_check s ch1 then
  (
    if cp.termination_check s ch2 then
    (
      pp.lemma_update_term_inj2 s x x ch1 ch2;
      assert (injective_precond bp.ch_t_bare_parser b1 b2);
      assert ((l01 <: nat) = (l02 <: nat))
    )
    else
      pp.lemma_update_term_next_non_intersect s x x ch1 ch2 ret1 ret2
  )
  else
  (
    if cp.termination_check s ch2 then
      pp.lemma_update_term_next_non_intersect s x x ch2 ch1 ret2 ret1
    else
    (
      let s'1 = cp.next_state s ch1 in
      let s'2 = cp.next_state s ch2 in
      let x'1 = dp.update_next s x ch1 in
      let x'2 = dp.update_next s x ch2 in
      let _ = bp.ch_t_bare_parser_valid b1 in
      let (b'1 : bytes{Seq.length b'1 < Seq.length b1}) = Seq.slice b1 l01 (Seq.length b1) in
      let _ = bp.ch_t_bare_parser_valid b2 in
      let (b'2 : bytes{Seq.length b'2 < Seq.length b2}) = Seq.slice b2 l02 (Seq.length b2) in
      if s'1 = s'2 then
      (
        let _ = automata_bare_parser'_pf1_aux cp dp bp pp s'1 x'1 x'2 b'1 b'2 in
        pp.lemma_update_next_inj2 s x x ch1 ch2;
        assert (injective_precond bp.ch_t_bare_parser b1 b2);
        assert ((l01 <: nat) = (l02 <: nat));
        let _ = automata_bare_parser'_pf3_aux cp dp bp pp s'1 x'1 b'1 b'2 in
        _
      )
      else
      (
        pp.lemma_update_next_non_intersect s x x ch1 ch2 ret1 ret2
      )
    )
  )

let automata_bare_parser'_pf3
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
  (x : dp.partial_t {dp.pre_t s x})
: Lemma (injective (automata_bare_parser' cp dp bp s x))
= Classical.forall_intro_2 (fun b1 b2 -> Classical.move_requires (automata_bare_parser'_pf3_aux cp dp bp pp s x b1) b2)

let automata_bare_parser'_pf23
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
  (x : dp.partial_t {dp.pre_t s x})
: Lemma (parser_kind_prop automata_default_parser_kind (automata_bare_parser' cp dp bp s x))
= parser_kind_prop_equiv automata_default_parser_kind (automata_bare_parser' cp dp bp s x);
  automata_bare_parser'_pf2 cp dp bp pp s x;
  automata_bare_parser'_pf3 cp dp bp pp s x
 
let automata_bare_parser'_pf
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
: Lemma (
  (forall s. and_then_cases_injective_dep (dp.post_t s) (automata_bare_parser' cp dp bp s)) /\
  (forall s data. parser_kind_prop automata_default_parser_kind (automata_bare_parser' cp dp bp s data)))
= Classical.forall_intro (fun s -> automata_bare_parser'_pf1 cp dp bp pp s);
  Classical.forall_intro_2 (fun s data -> automata_bare_parser'_pf23 cp dp bp pp s data)
  
let automata_parser
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (pp : automata_parser_param cp dp bp)
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
: (parser automata_default_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
= let _ = automata_bare_parser'_pf cp dp bp pp in
  automata_bare_parser' cp dp bp s data

let base_parser_kind = {
  parser_kind_low = 1;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let automata_parser_kind = {
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let automata_parser_body_rhs
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (automata_bare_parser_body: (
    (s : cp.control_t) ->
    (data : dp.partial_t {dp.pre_t s data}) ->
    Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
  ))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (ch: parse_filter_refine (fun ch -> not (cp.fail_check s ch)))
: Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
= 
      if cp.termination_check s ch
      then
        weaken automata_parser_kind (parse_ret (dp.update_term s data ch))
      else
        let s' = cp.next_state s ch in
        let data' = dp.update_next s data ch in
        automata_bare_parser_body s' data'
        `parse_synth`
        (fun ret ->
          id_cast dp.ret_t (dp.post_t s' data') (dp.post_t s data) (dp.lemma_cast_ret s data ch) ret
        )

let bp_of (cp : automata_control_param)
 (bp: parser base_parser_kind cp.ch_t) : Tot (automata_bare_parser_param cp) =
 {
  ch_t_bare_parser = bp;
  ch_t_bare_parser_valid = (fun _ -> parser_kind_prop_equiv base_parser_kind bp);
 }

let automata_bare_parser_body_erase_refinement
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (s : cp.control_t)
  (automata_bare_parser_body: (
    (data : dp.partial_t {dp.pre_t s data}) ->
    Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
  ))
  (data : dp.partial_t {dp.pre_t s data})
: Tot (parser automata_parser_kind dp.ret_t)
= automata_bare_parser_body data `parse_synth` (fun x -> x <: dp.ret_t)

let automata_parser_body_rhs_and_then_cases_injective
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (automata_bare_parser_body: (
    (s : cp.control_t) ->
    (data : dp.partial_t {dp.pre_t s data}) ->
    Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
  ))
  (automata_bare_parser_body_inj: (
    (s: cp.control_t) ->
    Lemma
    (and_then_cases_injective (automata_bare_parser_body_erase_refinement cp dp bp s (automata_bare_parser_body s)))
  ))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
: Lemma
  (and_then_cases_injective
    (automata_parser_body_rhs cp dp automata_bare_parser_body s data)
  )
= and_then_cases_injective_intro
    (automata_parser_body_rhs cp dp automata_bare_parser_body s data)
    (fun (ch1 ch2: parse_filter_refine _) x1 x2 ->
      assert_norm (automata_parser_body_rhs cp dp automata_bare_parser_body s data ch1 == (
        if cp.termination_check s ch1
        then
          weaken automata_parser_kind (parse_ret (dp.update_term s data ch1))
        else
          let s' = cp.next_state s ch1 in
          let data' = dp.update_next s data ch1 in
          automata_bare_parser_body s' data'
          `parse_synth`
          (fun ret ->
            id_cast dp.ret_t (dp.post_t s' data') (dp.post_t s data) (dp.lemma_cast_ret s data ch1) ret
          )
      ));
      assert_norm (automata_parser_body_rhs cp dp automata_bare_parser_body s data ch2 == (
        if cp.termination_check s ch2
        then
          weaken automata_parser_kind (parse_ret (dp.update_term s data ch2))
        else
          let s' = cp.next_state s ch2 in
          let data' = dp.update_next s data ch2 in
          automata_bare_parser_body s' data'
          `parse_synth`
          (fun ret ->
            id_cast dp.ret_t (dp.post_t s' data') (dp.post_t s data) (dp.lemma_cast_ret s data ch2) ret
          )
      ));
      if cp.termination_check s ch1 then
      (
        let ret1 = dp.update_term s data ch1 in
        if cp.termination_check s ch2 then
          pp.lemma_update_term_inj2 s data data ch1 ch2
        else
          let s2' = cp.next_state s ch2 in
          let data2' = dp.update_next s data ch2 in
          let _ = parse_synth_eq (automata_bare_parser_body s2' data2') (fun ret ->
            id_cast dp.ret_t (dp.post_t s2' data2') (dp.post_t s data) (dp.lemma_cast_ret s data ch2) ret
          ) x2 in
          let Some (ret2, _) = parse (automata_bare_parser_body s2' data2') x2 in
          pp.lemma_update_term_next_non_intersect s data data ch1 ch2 ret1 ret2
      )
      else
      (
        let s1' = cp.next_state s ch1 in
        let data1' = dp.update_next s data ch1 in
        let _ = parse_synth_eq (automata_bare_parser_body s1' data1') (fun ret ->
          id_cast dp.ret_t (dp.post_t s1' data1') (dp.post_t s data) (dp.lemma_cast_ret s data ch1) ret
        ) x1 in
        let Some (ret1, _) = parse (automata_bare_parser_body s1' data1') x1 in
        if cp.termination_check s ch2 then
          let ret2 = dp.update_term s data ch2 in
          pp.lemma_update_term_next_non_intersect s data data ch2 ch1 ret2 ret1
        else
        (
          let s2' = cp.next_state s ch2 in
          let data2' = dp.update_next s data ch2 in
          let _ = parse_synth_eq (automata_bare_parser_body s2' data2') (fun ret ->
            id_cast dp.ret_t (dp.post_t s2' data2') (dp.post_t s data) (dp.lemma_cast_ret s data ch2) ret
          ) x2 in
          let Some (ret2, _) = parse (automata_bare_parser_body s2' data2') x2 in
          let _ : squash (s1' == s2') =
            Classical.move_requires (pp.lemma_update_next_non_intersect s data data ch1 ch2 ret1) ret2
          in
          automata_bare_parser_body_inj s1';
          assert_norm (automata_bare_parser_body_erase_refinement cp dp bp s1' (automata_bare_parser_body s1') data1' == parse_synth (automata_bare_parser_body s1' data1') (fun x -> x <: dp.ret_t));
          assert_norm (automata_bare_parser_body_erase_refinement cp dp bp s2' (automata_bare_parser_body s2') data2' == parse_synth (automata_bare_parser_body s2' data2') (fun x -> x <: dp.ret_t));
          parse_synth_eq (automata_bare_parser_body s1' data1') (fun x -> x <: dp.ret_t) x1;
          parse_synth_eq (automata_bare_parser_body s2' data2') (fun x -> x <: dp.ret_t) x2;
          assert (and_then_cases_injective_precond (automata_bare_parser_body_erase_refinement cp dp bp s1' (automata_bare_parser_body s1')) data1' data2' x1 x2);
          pp.lemma_update_next_inj2 s data data ch1 ch2
        )
      )
    )

let automata_parser_body
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (automata_bare_parser_body: (
    (s : cp.control_t) ->
    (data : dp.partial_t {dp.pre_t s data}) ->
    Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
  ))
  (automata_bare_parser_body_inj: (
    (s: cp.control_t) ->
    Lemma
    (and_then_cases_injective (automata_bare_parser_body_erase_refinement cp dp bp s (automata_bare_parser_body s)))
  ))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
: Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
= automata_parser_body_rhs_and_then_cases_injective cp dp bp pp automata_bare_parser_body automata_bare_parser_body_inj s data;
  weaken
    automata_parser_kind
    (bp `parse_filter` (fun ch -> (not (cp.fail_check s ch))) `and_then` automata_parser_body_rhs cp dp automata_bare_parser_body s data)

noeq
type automata_parser_t
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
= {
    abp_parse: (
      (s : cp.control_t) ->
      (data : dp.partial_t {dp.pre_t s data}) ->
      Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
    );
    abp_body_inj: (
      (s : cp.control_t) ->
      Lemma
      (ensures (and_then_cases_injective (automata_bare_parser_body_erase_refinement cp dp bp s (abp_parse s))))
    );
  }

let rec automata_parser_3
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (fuel: nat)
: Tot (automata_parser_t cp dp bp)
  (decreases fuel)
= let phi
    (s : cp.control_t)
    (data : dp.partial_t {dp.pre_t s data})
  : Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
  = if fuel = 0
    then fail_parser automata_parser_kind _
    else automata_parser_body cp dp bp pp (automata_parser_3 cp dp bp pp (fuel - 1)).abp_parse (automata_parser_3 cp dp bp pp (fuel - 1)).abp_body_inj s data
  in
  let prf
    (s : cp.control_t)
  : Lemma
    (ensures (and_then_cases_injective (automata_bare_parser_body_erase_refinement cp dp bp s (phi s))))
  = assume False // TODO: replay automata_bare_parser'_pf1_aux
  in
  {
    abp_parse = phi;
    abp_body_inj = prf;
  }

let automata_parser_2
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (fuel: nat)
: (s : cp.control_t) ->
  (data : dp.partial_t {dp.pre_t s data}) -> parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret})
= (automata_parser_3 cp dp bp pp fuel).abp_parse

let automata_parser_body_inj
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (fuel: nat)
: (s : cp.control_t) ->
  Lemma
  (ensures (and_then_cases_injective (automata_bare_parser_body_erase_refinement cp dp bp s (automata_parser_2 cp dp bp pp fuel s))))
= (automata_parser_3 cp dp bp pp fuel).abp_body_inj

let rec automata_parser_2_eq
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (fuel: nat)
  (b : bytes)
: Lemma
  (requires (Seq.length b < fuel))
  (ensures (
    parse (automata_parser_2 cp dp bp pp fuel s data) b == parse (automata_bare_parser' cp dp (bp_of cp bp) s data) b
  ))
  (decreases fuel)
= assert_norm (automata_parser_2 cp dp bp pp fuel s data == (if fuel = 0
  then fail_parser automata_parser_kind _
  else automata_parser_body cp dp bp pp (automata_parser_2 cp dp bp pp (fuel - 1)) (automata_parser_body_inj cp dp bp pp (fuel - 1)) s data));
  assert (automata_parser_2 cp dp bp pp fuel s data == automata_parser_body cp dp bp pp (automata_parser_2 cp dp bp pp (fuel - 1)) (automata_parser_body_inj cp dp bp pp (fuel - 1)) s data);
  assert (parse (automata_parser_2 cp dp bp pp fuel s data) b == parse (automata_parser_body cp dp bp pp (automata_parser_2 cp dp bp pp (fuel - 1)) (automata_parser_body_inj cp dp bp pp (fuel - 1)) s data) b);
  automata_parser_body_rhs_and_then_cases_injective cp dp bp pp (automata_parser_2 cp dp bp pp (fuel - 1)) (automata_parser_body_inj cp dp bp pp (fuel - 1)) s data;
  assert_norm (automata_parser_body cp dp bp pp (automata_parser_2 cp dp bp pp (fuel - 1)) (automata_parser_body_inj cp dp bp pp (fuel - 1)) s data == 
    weaken
      automata_parser_kind
      (bp `parse_filter` (fun ch -> (not (cp.fail_check s ch))) `and_then` automata_parser_body_rhs cp dp (automata_parser_2 cp dp bp pp (fuel - 1)) s data)
    );
  parse_filter_eq bp (fun ch -> not (cp.fail_check s ch)) b;
  automata_parser_body_rhs_and_then_cases_injective cp dp bp pp (automata_parser_2 cp dp bp pp (fuel - 1)) (automata_parser_body_inj cp dp bp pp (fuel - 1)) s data;
  and_then_eq
    (parse_filter bp (fun ch -> not (cp.fail_check s ch)))
    (automata_parser_body_rhs cp dp (automata_parser_2 cp dp bp pp (fuel - 1)) s data)
    b;
  match parse (parse_filter bp (fun ch -> not (cp.fail_check s ch))) b with
  | None -> ()
  | Some (ch, consumed) ->
    let b' = Seq.slice b consumed (Seq.length b) in
    assert (parse (automata_parser_2 cp dp bp pp fuel s data) b == begin
      match parse (automata_parser_body_rhs cp dp (automata_parser_2 cp dp bp pp (fuel - 1)) s data ch) b' with
      | None -> None
      | Some (x, consumed') -> Some (x, consumed + consumed')
      end
    );
    assert_norm (automata_parser_body_rhs cp dp (automata_parser_2 cp dp bp pp (fuel - 1)) s data ch == (
      if cp.termination_check s ch
      then
        weaken automata_parser_kind (parse_ret (dp.update_term s data ch))
      else
        let s' = cp.next_state s ch in
        let data' = dp.update_next s data ch in
        automata_parser_2 cp dp bp pp (fuel - 1) s' data'
        `parse_synth`
        (fun ret ->
          id_cast dp.ret_t (dp.post_t s' data') (dp.post_t s data) (dp.lemma_cast_ret s data ch) ret
        )
    ));
    if cp.termination_check s ch
    then
      ()
    else begin
      let s' = cp.next_state s ch in
      let data' = dp.update_next s data ch in
      parse_synth_eq
        (automata_parser_2 cp dp bp pp (fuel - 1) s' data')
        (fun ret ->
          id_cast dp.ret_t (dp.post_t s' data') (dp.post_t s data) (dp.lemma_cast_ret s data ch) ret
        )
        b';
      parser_kind_prop_equiv base_parser_kind bp;
      automata_parser_2_eq cp dp bp pp s' data' (fuel - 1) b'
    end

let automata_parser_1
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (fuel: nat)
: Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
= automata_parser_2 cp dp bp pp fuel s data

let automata_parser_fuel_indep
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (fuel: nat)
  (b: bytes { Seq.length b < fuel })
: Lemma
  (ensures (automata_parser_1 cp dp bp pp s data fuel b == automata_parser_1 cp dp bp pp s data (Seq.length b + 1) b))
  (decreases fuel)
= automata_parser_2_eq cp dp bp pp s data fuel b;
  automata_parser_2_eq cp dp bp pp s data (Seq.length b + 1) b

let automata_parser_0
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
: Tot (parser automata_parser_kind (ret : dp.ret_t {dp.post_t s data ret}))
= LowParse.Spec.Fuel.close_by_fuel
    (automata_parser_1 cp dp bp pp s data)
    (fun b -> Seq.length b + 1)
    (automata_parser_fuel_indep cp dp bp pp s data)

let automata_parser_0_eq
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : parser base_parser_kind cp.ch_t)
  (pp : automata_parser_param cp dp (bp_of cp bp))
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (b : bytes)
: Lemma
  (
    parse (automata_parser_0 cp dp bp pp s data) b == parse (automata_bare_parser' cp dp (bp_of cp bp) s data) b
  )
= automata_parser_2_eq cp dp bp pp s data (Seq.length b + 1) b
