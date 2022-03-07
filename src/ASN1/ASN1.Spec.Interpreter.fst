module ASN1.Spec.Interpreter

include LowParse.Spec.Base
include LowParse.Spec.Combinators

include ASN1.Base
include ASN1.Spec.Content.BOOLEAN

include ASN1.Spec.ILC
include ASN1.Spec.Choice
include ASN1.Spec.Sequence

module List = FStar.List.Tot

let asn1_terminal_as_parser (k : asn1_terminal_k) : asn1_weak_parser (asn1_terminal_t k)  =
  match k with
  | ASN1_BOOLEAN -> weaken _ parse_asn1_boolean
  | _ -> fail_parser _ _  (* admit *)
(*
  | ASN1_INTEGER -> admit ()
  | ASN1_ENUM -> admit ()
  | ASN1_BITSTRING -> admit ()
  | ASN1_OCTETSTRING -> admit ()
  | ASN1_NULL -> admit ()
  | ASN1_OID -> admit ()
  | ASN1_ROID -> admit ()
  | ASN1_TIME -> admit ()
*)  

let rec asn1_content_as_parser (k : asn1_content_k) : Tot (asn1_weak_parser (asn1_content_t k)) (decreases k) =
  match k with
  | ASN1_TERMINAL k' -> asn1_terminal_as_parser k'
  | ASN1_SEQUENCE items pf -> make_asn1_sequence_parser (asn1_sequence_as_parser items)
  | ASN1_SEQUENCE_OF k' -> fail_parser _ _ (* admit Seq.seq (asn1_t k') *)
  | ASN1_SET_OF k' -> weaken _ (asn1_as_parser k')
  | ASN1_PREFIXED k' -> weaken _ (asn1_as_parser k')

and asn1_lc_as_parser (lc : list (asn1_id_t & asn1_content_k)) : Tot (lp : list (asn1_id_t & gen_parser) {asn1_lc_t lc == extract_types lp})  (decreases lc) =
  match lc with
  | [] -> [] 
  | h :: t -> 
    let (x, y) = h in
    (x, Mkgenparser (asn1_content_t y) (parse_asn1_LC (asn1_content_as_parser y))) :: (asn1_lc_as_parser t)

and asn1_as_parser (#s : _) (k : asn1_k s) : Tot (asn1_strong_parser (asn1_t k)) (decreases k) =
  match k with
  | ASN1_ILC id k' -> parse_asn1_ILC id (asn1_content_as_parser k')
  | ASN1_CHOICE_ILC lc pf -> make_asn1_choice_parser lc pf k (asn1_lc_as_parser lc)

and asn1_as_parser_twin (#s : _) (k : asn1_k s) : Tot (asn1_strong_parser (asn1_t k) & (fp : (asn1_id_t -> asn1_strong_parser (asn1_t k)) {and_then_cases_injective fp})) (decreases k) =
  match k with
  | ASN1_ILC id k' -> 
    let p = asn1_content_as_parser k' in
    let _ = parser_asn1_ILC_twin_case_injective id p in
    (parse_asn1_ILC id p, parse_asn1_ILC_twin id p)
  | ASN1_CHOICE_ILC lc pf ->
    let lp = asn1_lc_as_parser lc in
    let _ = make_asn1_choice_parser_twin_cases_injective lc pf k lp in
    (make_asn1_choice_parser lc pf k lp, make_asn1_choice_parser_twin lc pf k lp)

and asn1_decorated_as_parser (item : asn1_gen_item_k) : Tot (gp : gen_decorated_parser_twin {Mkgendcparser?.d gp == item}) =
  match item with
  | (| _, _, dk |) -> match dk with
                    | ASN1_PLAIN_ILC k -> 
                      let (p, fp) = asn1_as_parser_twin k in
                      Mkgendcparser item p fp
                    | ASN1_OPTION_ILC k -> 
                      let (p, fp) = asn1_as_parser_twin k in
                      Mkgendcparser item p fp
                    | ASN1_DEFAULT_TERMINAL id #k defv ->
                      let p = asn1_terminal_as_parser k in
                      Mkgendcparser item (parse_asn1_ILC id #(ASN1_TERMINAL k) p) (parse_asn1_ILC_twin id #(ASN1_TERMINAL k) p)

and asn1_sequence_as_parser (items : list asn1_gen_item_k) : Tot (lp : list gen_decorated_parser_twin {List.map (Mkgendcparser?.d) lp == items}) (decreases items) =
  match items with
  | [] -> []
  | hd :: tl -> (asn1_decorated_as_parser hd) :: (asn1_sequence_as_parser tl)
  
