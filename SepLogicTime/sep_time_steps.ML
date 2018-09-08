(* Setup for timed version of separation logic *)

signature SEP_TIME_STEPS =
sig
  val split_nat_one_term:
      Proof.context -> box_id * (term * term) -> (box_id * thm) list
  val split_nat: Proof.context -> box_id * (term * term) -> (box_id * thm) list
  val split_nat_gen:
      Proof.context -> box_id * (term * term) -> (box_id * thm) list

  val time_assn_matcher: assn_matcher
  val add_time_proofsteps: theory -> theory
end;

functor SepTimeSteps(SepUtil : SEP_UTIL) : SEP_TIME_STEPS =
struct

open SepUtil
open SepTimeUtil
structure AssnMatcher = AssnMatcher(SepUtil)
structure SepLogic = SepLogic(SepUtil)

val plus_ac_info = Nat_Util.plus_ac_on_typ @{theory} natT

(* Given natural numbers m and n, return the theorem m + n = p. *)
fun plus_eq_th m n =
    let
      val expr = Const (@{const_name plus}, natT --> natT --> natT)
                       $ mk_nat m $ mk_nat n
    in
      expr |> Thm.cterm_of @{context} |> Nat_Util.nat_fold_conv
    end

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
            val th = meta_sym (plus_eq_th coeff (coeff' - coeff))

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
                  val th' = [th, entail_th] MRS entails_trans2_th

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

val apply_to_precond = apply_to_thm' o Conv.arg_conv o Util.argn_conv 0

fun time_credit_ge_prfstep_fn ctxt item1 item2 =
    if SepLogic.is_implies_item item1 then [] else
    let
      val {id = id1, prop, ...} = item1
      val (P, _, _) = prop |> prop_of' |> dest_not |> dest_hoare_triple
      val Ps = ACUtil.dest_ac assn_ac_info P
      val opt_P' = find_first is_time_credit Ps
    in
      if is_none opt_P' then []
      else let
        val P' = the opt_P'

        val {id = id2, prop = prop2, ...} = item2
        val (a, _) = prop2 |> prop_of' |> Util.dest_binop_args
        val id = BoxID.merge_boxes ctxt (id1, id2)

        val b = dest_time_credit P'
        val split_res = (split_nat_gen ctxt (id, (b, a)))
                            |> filter (BoxID.has_incr_id o fst)

        fun process_split_nat (id', eq_th) =
            (* eq_th is b == a + p. P is $b or R * $b. prop2 is a >=_t a'. *)
            if length Ps = 1 then
              let
                val prop' = prop |> apply_to_precond (
                      Conv.arg_conv (Conv.rewr_conv eq_th))
                val th' = [prop2, prop'] MRS @{thm gc_time_hoare''}
              in
                [SepLogic.hoare_goal_update ctxt (id', th'),
                 ShadowItem {id = id', item = item1},
                 ShadowItem {id = id', item = item2}]
              end
            else
              let
                val prop' = prop |> apply_to_precond (
                      Conv.every_conv [
                        ACUtil.move_outmost assn_ac_info P',
                        Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv eq_th))])
                val th' = [prop2, prop'] MRS @{thm gc_time_hoare'}
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
     func = TwoStep time_credit_ge_prfstep_fn}

val add_time_proofsteps =
    fold AssnMatcher.add_assn_matcher [
      time_assn_matcher_gen

    ] #> fold add_prfstep [
      time_credit_ge_prfstep
    ]

end  (* structure SepTimeSteps *)
