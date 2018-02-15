(* Setup for timed version of separation logic *)

signature SEP_TIME_STEPS =
sig
  val split_nat_one_term:
      Proof.context -> box_id * (term * term) -> (box_id * thm) list
  val split_nat: Proof.context -> box_id * (term * term) -> (box_id * thm) list
  val split_nat_gen:
      Proof.context -> box_id * (term * term) -> (box_id * thm) list

  val time_assn_matcher: assn_matcher
  val disj_use_vardef_pair_prfstep: proofstep
  val add_time_proofsteps: theory -> theory
end;

structure SepTimeSteps : SEP_TIME_STEPS =
struct

open SepUtil
open SepTimeUtil

val plus_ac_info = Nat_Util.plus_ac_on_typ @{theory} natT

(* Assumes n is a single term. *)
fun split_nat_one_term ctxt (id, (m, n)) =
    let
      val (arg, coeff) = NatRing.dest_monomial n

      val ms = ACUtil.dest_ac plus_ac_info m

      (* Return the equality arg' == arg *)
      fun find_arg m' =
          let
            val (arg', coeff') = NatRing.dest_monomial m'
          in
            if coeff' < coeff then []
            else
              let
                val (carg', carg) = apply2 (Thm.cterm_of ctxt) (arg', arg)
              in
                map (pair m') (RewriteTable.equiv_info ctxt id (carg', carg))
              end
          end

      val args = maps find_arg ms

      fun process_arg (m', (id', eq_th)) =
          let
            (* coeff' >= coeff, m' = arg' * coeff', eq_th is arg' == arg *)
            val (_, coeff') = NatRing.dest_monomial m'

            (* coeff' == coeff + (coeff' - coeff) *)
            val th = meta_sym (Nat_Util.plus_eq_th coeff (coeff' - coeff))

            (* m' = n + p *)
            val th' =
                m' |> Thm.cterm_of ctxt
                   |> Conv.every_conv [NatRing.norm_monomial,
                                       Conv.arg1_conv (Conv.rewr_conv eq_th),
                                       Conv.arg_conv (Conv.rewr_conv th),
                                       rewr_obj_eq @{thm nat_distrib(2)}]

            (* m = n + p *)
            val th'' =
                if length ms > 1 then
                  m |> Thm.cterm_of ctxt
                    |> Conv.every_conv [ACUtil.move_outmost plus_ac_info m',
                                        Conv.arg_conv (Conv.rewr_conv th'),
                                        ACUtil.swap_r_cv plus_ac_info]
                else th'
          in
            (id', apply_to_rhs (Conv.binop_conv NatRing.norm_full) th'')
          end
    in
      map process_arg args
    end

(* Given natural number expressions m and n, attempt to write m as n +
   p. Return SOME (m = n + p) if successful, and NONE otherwise.
 *)
fun split_nat ctxt (id, (m, n)) =
    if not (UtilArith.is_plus n) then
      split_nat_one_term ctxt (id, (m, n))
    else let
      val (arg1, arg2) = Util.dest_binop_args n
      val split1 = split_nat ctxt (id, (m, arg1))
      fun process_split1 (id', th) =
          (* th: m == arg1 + p. *)
          let
            val p = th |> Util.rhs_of |> dest_arg
            val split2 = split_nat_one_term ctxt (id', (p, arg2))
            fun process_split2 (id'', th2) =
                (* th2: p == arg2 + p' *)
                (id'', m |> Thm.cterm_of ctxt
                         |> Conv.every_conv [Conv.rewr_conv th,
                                             Conv.arg_conv (Conv.rewr_conv th2),
                                             ACUtil.assoc_sym_cv plus_ac_info])
                 in
            map process_split2 split2
          end
    in
      maps process_split1 split1
    end

fun norm_length_full ctxt ct =
    let
      val ths = [@{thm List.list.size(3)}, @{thm length_Cons}]
    in
      Conv.every_conv [
        Conv.top_conv (fn _ => Conv.try_conv (
                                Conv.first_conv (map rewr_obj_eq ths))) ctxt,
        NatRing.norm_full] ct
    end

fun split_nat_gen ctxt (id, (m, n)) =
    let
      val cm = Thm.cterm_of ctxt m
      fun process_head_equiv (id', eq_th) =
          let
            val eq_th_m = apply_to_rhs (norm_length_full ctxt) eq_th
            val eq_th_n = norm_length_full ctxt (Thm.cterm_of ctxt n)

            val m' = Util.rhs_of eq_th_m  (* m = m' *)
            val n' = Util.rhs_of eq_th_n  (* n = n' *)
            fun process_split (id'', eq_th') =
                (* eq_th' is m' == n' + p *)
                (id'', cm |> Conv.every_conv [
                   Conv.rewr_conv eq_th_m,
                   Conv.rewr_conv eq_th',
                   Conv.arg1_conv (Conv.rewr_conv (meta_sym eq_th_n))])
          in
            if Util.rhs_of eq_th aconv m orelse UtilArith.is_plus m' orelse
               UtilArith.is_numc m' then
              map process_split (split_nat ctxt (id', (m', n')))
            else []
          end
    in
      cm |> RewriteTable.get_head_equiv ctxt
         |> BoxID.merge_box_with_info ctxt id
         |> maps process_head_equiv
    end

fun time_assn_matcher ctxt (pat, ct) (id, inst) =
    if Util.has_vars pat orelse not (is_time_credit pat) orelse
       not (is_time_credit (Thm.term_of ct)) then []
    else let
      val t = Thm.term_of ct
      val m = dest_time_credit t
      val n = dest_time_credit pat
    in
      if m aconv n then
        []  (* triv_assn_matcher can take care of this *)
      else let
        val splits = split_nat_gen ctxt (id, (m, n))
        fun process_split (id', eq_th) =
            (* eq_th is m == n + p for some p *)
            let
              val cv = Conv.every_conv [
                    Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv eq_th)),
                    Conv.arg_conv (rewr_obj_eq @{thm time_credit_add})]
              val th = t |> entail_triv_th ctxt
                         |> apply_to_thm' cv
            in
              ((id', inst), th)
            end
      in
        map process_split splits
      end
    end

fun time_assn_matcher_gen ctxt (pat, ct) (id, inst) =
    if Util.has_vars pat orelse not (is_time_credit pat) then []
    else let
      val cts = ACUtil.cdest_ac assn_ac_info ct

      fun match_i i =
          let
            val ct' = nth cts i
            val insts = time_assn_matcher ctxt (pat, ct') (id, inst)

            (* entail_th is of form pat(inst') ==> t' * t''. *)
            fun process_inst ((id', inst'), entail_th) =
                let
                  val move_outmost = ACUtil.move_outmost assn_ac_info
                  val t' = Thm.term_of ct'

                  (* th: ct ==> rest * pat(inst') *)
                  val th = ct |> Thm.term_of
                              |> entail_triv_th ctxt
                              |> apply_to_entail_r (move_outmost t')

                  (* th': ct ==> rest * (t' * t'') *)
                  val th' = [th, entail_th] MRS @{thm entail_trans2}

                  (* th'': ct ==> (rest * t'') * t' *)
                  val th'' = th' |> apply_to_entail_r
                                 (Conv.every_conv [
                                     Conv.arg_conv (ACUtil.comm_cv assn_ac_info),
                                     ACUtil.assoc_sym_cv assn_ac_info])
                in
                  ((id', inst'), th'')
                end
          in
            map process_inst insts
          end
    in
      if length cts = 1 then
        time_assn_matcher ctxt (pat, ct) (id, inst)
      else
        maps match_i (0 upto (length cts - 1))
    end

fun time_credit_ge_prfstep_fn ictxt item1 item2 =
    if SepLogic.is_implies_item item1 then [] else
    let
      val {id = id1, prop, ...} = item1
      val (P, _, _) = prop |> prop_of' |> dest_not |> dest_hoare_triple
      val Ps = ACUtil.dest_ac assn_ac_info P
      val P' = List.last Ps
      val ctxt = IncrContext.context_of ictxt

      val {id = id2, prop = prop2, ...} = item2
      val (a, _) = prop2 |> prop_of' |> Util.dest_binop_args
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      if not (is_time_credit P') then []
      else let
        val b = dest_time_credit P'
        val split_res = (split_nat_gen ctxt (id, (b, a)))
                            |> IncrContext.replace_id_for_type' ictxt

        fun process_split_nat (id', eq_th) =
            (* eq_th is b == a + p. P is $b or R * $b. prop2 is a >=_t a'. *)
            let
              val P_cv = if length Ps = 1 then
                           Conv.arg_conv (Conv.rewr_conv eq_th)
                         else
                           Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv eq_th))

              val prop' = prop |> apply_to_thm' (
                    Conv.arg_conv (Util.argn_conv 0 P_cv))
              val th' = if length Ps = 1 then
                          [prop2, prop'] MRS @{thm gc_time_hoare''}
                        else
                          [prop2, prop'] MRS @{thm gc_time_hoare'}
            in
              [SepLogic.hoare_goal_update ctxt (id', th'),
               ShadowItem {id = id', item = item1},
               ShadowItem {id = id', item = item2}]
            end
      in
        maps process_split_nat split_res
      end
    end

val time_credit_ge_prfstep =
    {name = "sep_time.time_credit_ge",
     args = [TypedUniv SepLogic.TY_CODE_POS,
             TypedMatch (TY_PROP, @{term_pat "time_credit_ge ?b ?a"})],
     priority = PRIORITY_URGENT,
     func = TwoStep time_credit_ge_prfstep_fn}

fun swap_disj ct =
    Conv.every_conv [rewr_obj_eq (obj_sym UtilBase.disj_assoc_th),
                     Conv.arg1_conv (rewr_obj_eq UtilBase.disj_commute_th),
                     rewr_obj_eq UtilBase.disj_assoc_th] ct

fun move_outmost u ct =
    let
      val t = Thm.term_of ct
    in
      if u aconv t then Conv.all_conv ct
      else if not (is_disj t) then
        raise Fail "move_outmost: u not found in ct."
      else let
        val (a, b) = Util.dest_binop_args t
      in
        if u aconv a then Conv.all_conv ct
        else if is_disj b then
          Conv.every_conv [Conv.arg_conv (move_outmost u),
                           swap_disj] ct
        else if u aconv b then
          rewr_obj_eq UtilBase.disj_commute_th ct
        else
          raise Fail "move_outmost: u not found in ct."
      end
    end

fun is_prod t =
    case t of
        Const (@{const_name Pair}, _) $ _ $ _ => true
      | _ => false

fun disj_use_vardef_pair ictxt item =
    if not (IncrContext.is_single_ictxt ictxt) then []
    else if Logic_ProofSteps.is_match_prem_only item then []
    else let
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, prop, ...} = item
      val (disj_head, csubs) = Logic_ProofSteps.dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
      val len = length subs
      fun is_vardef t =
          is_eq_term t andalso
          let val t1 = dest_arg1 t in
            is_prod t1 andalso
            is_Var (dest_arg1 t1) andalso is_Var (dest_arg t1)
          end
    in
      if len = 1 then [] else
      case find_first (is_vardef o get_neg) subs of
          NONE => []
        | SOME t =>
          let
            val (t1, _) = dest_eq (get_neg t)
            val (v1, v2) = (dest_arg1 t1, dest_arg t1)
            val cv = Conv.every_conv [
                  move_outmost t,
                  rewr_obj_eq (obj_sym UtilBase.imp_conv_disj_th)]
            val prop' =
                prop |> apply_to_thm' cv
                     |> fold Thm.forall_intr (map (Thm.cterm_of ctxt) [v2, v1])
                     |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
                     |> apply_to_thm' (rewr_obj_eq @{thm use_vardef_pair})
          in
            [ShadowItem {id = id, item = item},
             Logic_ProofSteps.disj_to_update
                 false disj_head (id, SOME (len - 1), prop')]
          end
    end

val disj_use_vardef_pair_prfstep =
    {name = "disj_use_vardef_pair",
     args = [TypedUniv TY_DISJ],
     priority = PRIORITY_NORM,
     func = OneStep disj_use_vardef_pair}

val add_time_proofsteps =
    fold add_assn_matcher [
      time_assn_matcher_gen

    ] #> fold add_prfstep [
      time_credit_ge_prfstep, disj_use_vardef_pair_prfstep
    ]

end  (* structure SepTimeSteps *)

val _ = Theory.setup (SepTimeSteps.add_time_proofsteps)
