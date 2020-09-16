theory SLTC_Automation
imports
  "HOL-Eisbach.Eisbach" SLTC_More Automatic_Refinement.Automatic_Refinement
 
begin


subsection \<open>Experiment TOMOVE\<close>
lemma run_and_execute: "(\<forall>\<sigma> t r. run c (Some h) \<sigma> r t \<longrightarrow> \<sigma> \<noteq> None \<and> P (the \<sigma>) r t)
        \<longleftrightarrow> (\<exists>h' t r. execute c h = Some (r, h', t) \<and> P h' r t)"  
  apply rule
  subgoal by (metis option.sel run.intros(2) run.intros(3) timeFrame.elims) 
  subgoal by (metis (mono_tags) not_None_eq option.sel prod.sel(1) prod.sel(2) run_to_execute) 
  done


subsection \<open>stuff for VCG\<close>

lemma is_hoare_triple: "<P> c <Q> \<Longrightarrow> <P> c <Q>" .

theorem normalize_rules:
           "\<And>P. (\<And>x. <P x> f <Q>) \<Longrightarrow> <\<exists>\<^sub>Ax. P x> f <Q>"
           "\<And>P. (b \<Longrightarrow> <P> f <Q>) \<Longrightarrow> <P * \<up> b> f <Q>"
           "\<And>P. (b \<Longrightarrow> <emp> f <Q>) \<Longrightarrow> <\<up> b> f <Q>"
  subgoal using pre_ex_rule by force
  subgoal using norm_pre_pure_iff by blast
  subgoal using norm_pre_pure_iff2 by blast
  done
    

subsection "Rotate method"

definition gr where "gr A B = A * B"

lemma right_swap: "(A \<Longrightarrow>\<^sub>A B * (C * D)) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (D * C))"
  by (simp add: assn_times_comm)
lemma right_take: "(A \<Longrightarrow>\<^sub>A gr B C * D) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A B * (C * D))"
  by (simp add: gr_def assn_times_assoc) 
lemma left_swap: "(B * (C * D) \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (D * C) \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)
lemma left_take: "(gr B C * D \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (B * (C * D) \<Longrightarrow>\<^sub>A A)"
  by (simp add: gr_def assn_times_assoc) 

lemma right_move_back: "(A \<Longrightarrow>\<^sub>A B * C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A C * B)"
  by (simp add: assn_times_comm)
lemma left_move_back: "(B * C \<Longrightarrow>\<^sub>A A) \<Longrightarrow> (C * B \<Longrightarrow>\<^sub>A A)"
  by (simp add: assn_times_comm)
lemma right_move_backt: "(A \<Longrightarrow>\<^sub>t B * C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>t C * B)"
  by (simp add: assn_times_comm)
lemma left_move_backt: "(B * C \<Longrightarrow>\<^sub>t A) \<Longrightarrow> (C * B \<Longrightarrow>\<^sub>t A)"
  by (simp add: assn_times_comm)

thm mult.assoc
method rotater = ( (simp only: mult.assoc)? , rule right_move_back , (simp only: mult.assoc)?  )
method rotatel = ( (simp only: mult.assoc)? , rule left_move_back , (simp only: mult.assoc)?  )

method swapl = ( (simp only: mult.assoc)? ,rule left_swap, (simp only: mult.assoc)?   )
method takel = ( (simp only: mult.assoc)? , rule left_take, (simp only: mult.assoc)?  )

method swapr = ( (simp only: mult.assoc)? , rule right_swap , (simp only: mult.assoc)?  )
method taker = ( (simp only: mult.assoc)? , rule right_take, (simp only: mult.assoc)?  )

method rotatert = ( (simp only: mult.assoc)? , rule right_move_backt , (simp only: mult.assoc)?  )
method rotatelt = ( (simp only: mult.assoc)? , rule left_move_backt , (simp only: mult.assoc)?  )


lemma match_firstt: "A \<Longrightarrow>\<^sub>t B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>t \<Gamma> * B"   
  by (simp add: entt_star_mono) 

lemma match_restt: "emp \<Longrightarrow>\<^sub>t B \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>t \<Gamma> * B"  
  using match_firstt by fastforce 

lemma match_first: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> * A \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  by (simp add: assn_times_comm entails_frame)  

lemma match_rest: "emp \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<Gamma> \<Longrightarrow>\<^sub>A \<Gamma> * B"  
  using match_first by fastforce 





subsection "Simplifier setup"


lemma is_entails: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P \<Longrightarrow>\<^sub>AQ" .
 
text \<open>Used by existential quantifier extraction tactic\<close>
lemma enorm_exI': (* Incomplete, as chosen x may depend on heap! *)
  "(\<And>x. Z x \<longrightarrow> (P \<Longrightarrow>\<^sub>A Q x)) \<Longrightarrow> (\<exists>x. Z x) \<longrightarrow> (P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. Q x))"
  by (metis ent_ex_postI)



lemmas solve_ent_preprocess_simps = 
  ent_pure_post_iff ent_pure_post_iff_sng ent_pure_pre_iff ent_pure_pre_iff_sng
lemmas ent_refl = entails_triv
lemmas ent_triv = ent_true ent_false
lemmas norm_assertion_simps =
  (* Neutral elements *)
  mult_1[where 'a=assn] mult_1_right[where 'a=assn]

  (* Zero elements *)
  false_absorb star_false_right

  time_credit_add[symmetric]
  ex_assn_move_out(1) pure_conj[symmetric]

  (* Duplicated References *)
  sngr_same_false snga_same_false

(*
theorem solve_ent_preprocess_simps:
            (?P \<Longrightarrow>\<^sub>A ?Q * \<up> ?b) = ((\<forall>h. h \<Turnstile> ?P \<longrightarrow> ?b) \<and> (?P \<Longrightarrow>\<^sub>A ?Q))
            (?P \<Longrightarrow>\<^sub>A \<up> ?b) = ((\<forall>h. h \<Turnstile> ?P \<longrightarrow> ?b) \<and> (?P \<Longrightarrow>\<^sub>A emp))
            (?P * \<up> ?b \<Longrightarrow>\<^sub>A ?Q) = (?b \<longrightarrow> (?P \<Longrightarrow>\<^sub>A ?Q))
            (\<up> ?b \<Longrightarrow>\<^sub>A ?Q) = (?b \<longrightarrow> (emp \<Longrightarrow>\<^sub>A ?Q)) *) 


subsection \<open>Frame Matcher\<close>
text \<open>Given star-lists P,Q and a frame F, this method tries to match 
  all elements of Q with corresponding elements of P. The result is a 
  partial match, that contains matching pairs and the unmatched content.\<close>

text \<open>The frame-matcher internally uses syntactic lists separated by
  star, and delimited by the special symbol \<open>SLN\<close>, which is defined
  to be \<open>emp\<close>.\<close>
definition [simp]: "SLN \<equiv> emp"
lemma SLN_left: "SLN * P = P" by simp
lemma SLN_right: "P * SLN = P" by simp

lemmas SLN_normalize = SLN_right mult.assoc[symmetric, where 'a=assn]
lemmas SLN_strip = SLN_right SLN_left mult.assoc[symmetric, where 'a=assn]

text \<open>A query to the frame matcher. Contains the assertions
  P and Q that shall be matched, as well as a frame F, that is not 
  touched.\<close>

definition [simp]: "FI_QUERY P Q F \<equiv> P \<Longrightarrow>\<^sub>A Q*F"

abbreviation "fi_m_fst M \<equiv> foldr ((*)) (map fst M) emp"
abbreviation "fi_m_snd M \<equiv> foldr ((*)) (map snd M) emp"
abbreviation "fi_m_match M \<equiv> (\<forall>(p,q)\<in>set M. p \<Longrightarrow>\<^sub>A q)"

text \<open>A result of the frame matcher. Contains a list of matching pairs,
  as well as the unmatched parts of P and Q, and the frame F.
\<close>
definition [simp]: "FI_RESULT M UP UQ F \<equiv> 
  fi_m_match M \<longrightarrow> (fi_m_fst M * UP \<Longrightarrow>\<^sub>A fi_m_snd M * UQ * F)"

text \<open>Internal structure used by the frame matcher: 
  m contains the matched pairs; p,q the assertions that still needs to be 
  matched; up,uq the assertions that could not be matched; and f the frame.
  p and q are SLN-delimited syntactic lists. 
\<close>

definition [simp]: "FI m p q up uq f \<equiv> 
  fi_m_match m \<longrightarrow> (fi_m_fst m * p * up \<Longrightarrow>\<^sub>A fi_m_snd m * q * uq * f)"

text \<open>Initialize processing of query\<close>
lemma FI_init: 
  assumes "FI [] (SLN*P) (SLN*Q) SLN SLN F"
  shows "FI_QUERY P Q F"
  using assms by simp

text \<open>Construct result from internal representation\<close>
lemma FI_finalize:
  assumes "FI_RESULT m (p*up) (q*uq) f"
  shows "FI m p q up uq f"
  using assms by (simp add: mult.assoc )

text \<open>Auxiliary lemma to show that all matching pairs together form
  an entailment. This is required for most applications.\<close>
lemma fi_match_entails:
  assumes "fi_m_match m"
  shows "fi_m_fst m \<Longrightarrow>\<^sub>A fi_m_snd m"
  using assms apply (induct m)
  apply (simp_all split: prod.split_asm add: ent_star_mono)
  done

text \<open>Internally, the frame matcher tries to match the first assertion
  of q with the first assertion of p. If no match is found, the first
  assertion of p is discarded. If no match for any assertion in p can be
  found, the first assertion of q is discarded.\<close>

text \<open>Match\<close>
lemma FI_match:
  assumes "p \<Longrightarrow>\<^sub>A q"
  assumes "FI ((p,q)#m) (ps*up) (qs*uq) SLN SLN f"
  shows "FI m (ps*p) (qs*q) up uq f"
  using assms unfolding FI_def
  apply (simp add: mult.assoc) 
  by (simp add: mult.left_commute) 

text \<open>No match\<close>
lemma FI_p_nomatch:
  assumes "FI m ps (qs*q) (p*up) uq f"
  shows "FI m (ps*p) (qs*q) up uq f"
  using assms unfolding FI_def
  by (simp add: mult.assoc)  

text \<open>Head of q could not be matched\<close>
lemma FI_q_nomatch:
  assumes "FI m (SLN*up) qs SLN (q*uq) f"
  shows "FI m SLN (qs*q) up uq f"
  using assms unfolding FI_def
  by (simp add: mult.assoc)  

subsection \<open>Frame Inference\<close>
lemma frame_inference_init:
  assumes "FI_QUERY P Q F"
  shows "P \<Longrightarrow>\<^sub>A Q * F"
  using assms by simp

lemma frame_inference_finalize:
  shows "FI_RESULT M F emp F"
  apply simp
  apply rule
  apply (drule fi_match_entails)
  apply (rule ent_star_mono[OF _ ent_refl])
  apply assumption
  done



subsection \<open>Frame Inference\<close>

definition [simp]: "TI_QUERY P Q F \<equiv> P = Q + F"
lemma TI_QUERYD: "P = Q + F \<Longrightarrow> TI_QUERY P Q F" by simp

lemma timeframe_inference_init:
  assumes
      "FI_QUERY P Q FH"   (* first do frame inference in order to instatiate schematics! *)
      "TI_QUERY T T' FT"
      "F = FH * $FT"
  shows "P * $T\<Longrightarrow>\<^sub>A (Q * F) * $T'"
  using assms apply (simp add: time_credit_add mult.assoc)
  apply(rotater) apply rotater apply rotatel apply rotatel apply(rule match_first)  apply rotatel apply (rule match_first)
  .

lemma timeframe_inference_init_normalize:
 "emp * $T\<Longrightarrow>\<^sub>A F * $T' \<Longrightarrow> $T\<Longrightarrow>\<^sub>A F * $T'"
  by auto


lemma dollarD: "a = b \<Longrightarrow> $a \<Longrightarrow>\<^sub>A $b"
  by simp

subsection \<open>Entailment Solver\<close>
lemma entails_solve_init:
  "FI_QUERY P (Q*$T) true \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q * true * $T"
  "FI_QUERY P Q true \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q * true"
  "FI_QUERY P Q emp \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q"
    apply (simp_all add: mult.assoc )   
  by (simp add:  mult.commute)  

lemma entails_solve_init_time':
  "FI_QUERY P (Q) true \<Longrightarrow> TI_QUERY T T' FT \<Longrightarrow>  P * $T \<Longrightarrow>\<^sub>A Q * true * $T'"
  apply simp 
  by (smt ent_star_mono gc_time le_add1 merge_true_star star_aci(2) star_aci(3))

lemma entails_solve_init_time:
  "FI_QUERY P (Q) true \<Longrightarrow> TI_QUERY T T' FT \<Longrightarrow>  P * $T \<Longrightarrow>\<^sub>A Q * true * $T'"
  "FI_QUERY P emp true \<Longrightarrow> TI_QUERY T T' FT \<Longrightarrow>  P * $T \<Longrightarrow>\<^sub>A true * $T'"
  "FI_QUERY emp Q true \<Longrightarrow> TI_QUERY T T' FT \<Longrightarrow>  $T \<Longrightarrow>\<^sub>A Q * true * $T'"
  "FI_QUERY emp Q true \<Longrightarrow> TI_QUERY T T' FT \<Longrightarrow>  $T \<Longrightarrow>\<^sub>A true * $T'"
  subgoal by(fact entails_solve_init_time')
  subgoal using entails_solve_init_time'[where Q=emp] by simp
  subgoal using entails_solve_init_time'[where P=emp] by simp
  subgoal using entails_solve_init_time'[where P=emp and Q=emp] by simp
  done

lemma entails_solve_finalize:
  "FI_RESULT M P emp true"
  "FI_RESULT M emp emp emp"
  by (auto simp add: fi_match_entails intro: ent_star_mono)


named_theorems sep_dflt_simps "Seplogic: Default simplification rules for automated solvers"
named_theorems sep_eintros "Seplogic: Intro rules for entailment solver"
named_theorems sep_heap_rules "Seplogic: VCG heap rules"
named_theorems sep_decon_rules "Seplogic: VCG deconstruct rules"




ML \<open>
infix 1 THEN_IGNORE_NEWGOALS

structure Seplogic_Auto =
struct


  (***********************************)
  (*          Method Setup           *)
  (***********************************)

  val dflt_simps_modifiers = [
    Args.$$$ "dflt_simps" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_dflt_simps}) \<^here>),
    Args.$$$ "dflt_simps" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_dflt_simps}) \<^here>)
  ];
  val heap_modifiers = [
    Args.$$$ "heap" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_heap_rules}) \<^here>),
    Args.$$$ "heap" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_heap_rules}) \<^here>)
  ];
  val decon_modifiers = [
    Args.$$$ "decon" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_decon_rules}) \<^here>),
    Args.$$$ "decon" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_decon_rules}) \<^here>)
  ];

  val eintros_modifiers = [
    Args.$$$ "eintros" -- Scan.option Args.add -- Args.colon 
      >> K (Method.modifier (Named_Theorems.add @{named_theorems sep_eintros}) \<^here>),
    Args.$$$ "eintros" -- Scan.option Args.del -- Args.colon 
      >> K (Method.modifier (Named_Theorems.del @{named_theorems sep_eintros}) \<^here>)
  ];

  val solve_entails_modifiers = dflt_simps_modifiers @ eintros_modifiers;

  val vcg_modifiers = 
    heap_modifiers @ decon_modifiers @ dflt_simps_modifiers;

  val sep_auto_modifiers = 
    clasimp_modifiers @ vcg_modifiers @ eintros_modifiers;


  (***********************************)
  (*        Custom Tacticals         *)
  (***********************************)

  (* Apply tac1, and then tac2 with an offset such that anything left 
     over by tac1 is skipped.

     The typical usage of this tactic is, if a theorem is instantiated
     with another theorem that produces additional goals that should 
     be ignored first. Here, it is used in the vcg to ensure that 
     frame inference is done before additional premises (that may 
     depend on the frame) are discharged.
  *)
  fun (tac1 THEN_IGNORE_NEWGOALS tac2) i st = let
    val np = Thm.nprems_of st
  in
    (tac1 i THEN (fn st' => let val np' = Thm.nprems_of st' in
      if np'<np then tac2 i st'
      else tac2 (i+(np'-np)+1) st'
    end)) st
  end;

  (***********************************)
  (*     Assertion Normalization     *)
  (***********************************)
  (* Find two terms in a list whose key is equal *)
  fun find_similar (key_of:term -> term) (ts:term list) = let
    fun frec _ [] = NONE
    | frec tab (t::ts) = let val k=key_of t in
      if Termtab.defined tab k then
        SOME (the (Termtab.lookup tab k),t)
      else frec (Termtab.update (k,t) tab) ts
    end
  in
    frec Termtab.empty ts
  end;

  (* Perform DFS over term with binary operator opN, threading through
    a state. Atomic terms are transformed by tr. Supports omission of
    terms from the result structure by transforming them to NONE. *)
  fun dfs_opr opN (tr:'state -> term -> ('state*term option)) 
    d (t as ((op_t as Const (fN,_))$t1$t2)) =
    if fN = opN then let
        val (d1,t1') = dfs_opr opN tr d t1;
        val (d2,t2') = dfs_opr opN tr d1 t2;
      in
        case (t1',t2') of
          (NONE,NONE) => (d2,NONE)
        | (SOME t1',NONE) => (d2,SOME t1')
        | (NONE,SOME t2') => (d2,SOME t2')
        | (SOME t1',SOME t2') => (d2,SOME (op_t$t1'$t2'))
      end
    else tr d t
  | dfs_opr _ tr d t = tr d t;
    
  (* Replace single occurrence of (atomic) ot in t by nt. 
    Returns new term or NONE if nothing was removed. *)
  fun dfs_replace_atomic opN ot nt t = let
    fun tr d t = if not d andalso t=ot then (true,SOME nt) else (d,SOME t);
    val (success,SOME t') = dfs_opr opN tr false t; 
  in
    if success then SOME t' else NONE
  end;

  fun assn_simproc_fun ctxt credex = let
    val ([redex],ctxt') = Variable.import_terms true [Thm.term_of credex] ctxt;
    val export = singleton (Variable.export ctxt' ctxt)

    fun mk_star t1 t2 = @{term "(*)::assn \<Rightarrow> _ \<Rightarrow> _"}$t2$t1;

    fun mk_star' NONE NONE = NONE
    | mk_star' (SOME t1) NONE  = SOME t1
    | mk_star' NONE (SOME t2) = SOME t2
    | mk_star' (SOME t1) (SOME t2) = SOME (mk_star t1 t2);

    fun ptrs_key (_$k$_) = k;

    fun remove_term pt t = case
      dfs_replace_atomic @{const_name "Groups.times_class.times"} pt 
        @{term emp} t 
    of
      SOME t' => t';  

    fun normalize t = let

      fun ep_tr (has_true,ps,ts,ptrs) t = case t of 
        Const (@{const_name "pure_assn"},_)$_ 
        => ((has_true,t::ps,ts,ptrs),NONE)
      | Const (@{const_name "sngr_assn"},_)$_$_ 
        => ((has_true,ps,ts,t::ptrs),SOME t)
      | Const (@{const_name "snga_assn"},_)$_$_
        => ((has_true,ps,ts,t::ptrs),SOME t)
      | Const (@{const_name "timeCredit_assn"},_)$_
        => ((has_true,ps,t::ts,ptrs),NONE)
      | Const (@{const_name "top_assn"},_)
        => ((true,ps,ts,ptrs),NONE)
      | (inf_op as Const (@{const_name "and_assn"},_))$t1$t2
        => ((has_true,ps,ts,ptrs),SOME (inf_op$normalize t1$normalize t2))
      | _ => ((has_true,ps,ts,ptrs),SOME t);

      fun normalizer t = case dfs_opr @{const_name "Groups.times_class.times"}
        ep_tr (false,[],[],[]) t 
      of 
        ((has_true,ps,ts,ptrs),rt) => 
            ((has_true,rev ps,rev ts,ptrs),rt);

      fun normalize_core t = let 
        val ((has_true,pures,tis,ptrs),rt) = normalizer t;
        val similar =  find_similar ptrs_key ptrs  ;
        val true_t = if has_true then SOME @{term "top_assn"} 
          else NONE;
        val pures' = case pures of 
            [] => NONE
          | p::ps => SOME (fold mk_star ps p);
        val tis' = case tis of 
            [] => NONE
          | p::ps => SOME (fold mk_star ps p);
      in
        case similar of NONE => the ((mk_star' pures' (mk_star' tis' (mk_star' true_t rt))) )
        | SOME (t1,t2) => let
            val t_stripped = remove_term t1 (remove_term t2 t);
          in mk_star t_stripped (mk_star t1 t2) 
          end
      end;

      fun skip_ex ((exq as Const (@{const_name "ex_assn"},_))$(Abs (n,ty,t))) =
        exq$Abs (n,ty,skip_ex t)
      | skip_ex t = normalize_core t;

      val (bs,t') = strip_abs t;
      val ty = fastype_of1 (map #2 bs,t');
    in
      if ty = @{typ assn} then
        Logic.rlist_abs (bs,skip_ex t')  
      else t
    end;

    (*val _ = tracing (tr_term redex);*)
    val (f,terms) = strip_comb redex;
    val nterms = map (fn t => let
        (*val _ = tracing (tr_term t); *)
        val t'=normalize t; 
        (*val _ = tracing (tr_term t');*)
      in t' end) terms;
    val new_form = list_comb (f,nterms);

    val res_ss = (put_simpset HOL_basic_ss ctxt addsimps @{thms star_aci});
    val result = Option.map (export o mk_meta_eq) (Arith_Data.prove_conv_nohyps
      [simp_tac res_ss 1] ctxt' (redex,new_form)
    );

  in 
    result
  end handle exc =>
    if Exn.is_interrupt exc then Exn.reraise exc
    else
      (tracing ("assn_simproc failed with exception\n:" ^ Runtime.exn_message exc);
        NONE) (* Fail silently *);


  val assn_simproc =
    Simplifier.make_simproc @{context} "assn_simproc"
     {lhss =
      [@{term "h \<Turnstile> P"},
       @{term "P \<Longrightarrow>\<^sub>A Q"},
       @{term "P \<Longrightarrow>\<^sub>t Q"} ,
       @{term "hoare_triple P c Q"} (*,
       @{term "(P::assn) = Q"} *)],
      proc = K assn_simproc_fun};


  (***********************************)
  (*     Default Simplifications     *)
  (***********************************)

  (* Default simplification. MUST contain assertion normalization!
    Tactic must not fail! *)
  fun dflt_tac ctxt = asm_full_simp_tac
    (put_simpset HOL_ss ctxt
      addsimprocs [assn_simproc] 
      addsimps @{thms norm_assertion_simps}
      addsimps (Named_Theorems.get ctxt @{named_theorems sep_dflt_simps})
      |> fold Splitter.del_split @{thms if_split}
    );


  (***********************************)
  (*         Frame Matcher           *)
  (***********************************)

  (* Do frame matching
    imp_solve_tac - tactic used to discharge first assumption of match-rule
      cf. lemma FI_match.
  *)
  fun match_frame_tac imp_solve_tac ctxt = let
    (* Normalize star-lists *)
    val norm_tac = simp_tac (
      put_simpset HOL_basic_ss ctxt addsimps @{thms SLN_normalize});

    (* Strip star-lists *)
    val strip_tac = 
      simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms SLN_strip}) THEN'
      simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms SLN_def});

    (* Do a match step *)
    val match_tac = resolve_tac ctxt @{thms FI_match} (* Separate p,q*)
      THEN' SOLVED' imp_solve_tac (* Solve implication *)
      THEN' norm_tac;

    (* Do a no-match step *)
    val nomatch_tac = resolve_tac ctxt @{thms FI_p_nomatch} ORELSE' 
      (resolve_tac ctxt @{thms FI_q_nomatch} THEN' norm_tac);
  in
    resolve_tac ctxt @{thms FI_init} THEN' norm_tac 
    THEN' REPEAT_DETERM' (FIRST' [
      CHANGED o dflt_tac ctxt,
      (match_tac ORELSE' nomatch_tac)])
    THEN' resolve_tac ctxt @{thms FI_finalize} THEN' strip_tac
  end;



  (***********************************)
  (*         Frame Inference         *)
  (***********************************)

  fun frame_inference_tac ctxt =
    resolve_tac ctxt @{thms frame_inference_init} 
    THEN' match_frame_tac (resolve_tac ctxt @{thms ent_refl}) ctxt
    THEN' resolve_tac ctxt @{thms frame_inference_finalize};

 

  (***********************************)
  (* Nat splitter  powerd by auto2   *)
  (***********************************)

  fun mytac ctxt a b = let 
        val _ = tracing (Syntax.string_of_term ctxt a)
      val _ = tracing (Syntax.string_of_term ctxt b) 
      val ths = map snd (SepTimeSteps.split_nat ctxt ([], (a, b))); 
   in
         (if length ths > 0 then  (EqSubst.eqsubst_tac ctxt [1] ths 
              THEN' FIRST' [ resolve_tac ctxt @{thms refl}, 
                             SOLVED' (simp_tac (put_simpset HOL_ss ctxt  addsimps @{thms mult.commute})) ] ) 1  else no_tac) end 

  fun split_nat_tac ctxt =
     Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} => ALLGOALS (
        SUBGOAL (fn (t, _) => case Logic.strip_imp_concl t of
          @{mpat "Trueprop (?a = ?b + _)"} => 
            mytac ctxt a b 
         |  _ => no_tac
        ))
      ) ctxt  
 
  (* assumes a goal of form "a = b + c",
      normalizes a and b using NatRing.norm_full *)
  fun normalize_time_goal ctxt = 
     (CONVERSION (Conv.params_conv ~1 (fn _ =>
              (Conv.concl_conv ~1 
               (Conv.arg_conv (Conv.every_conv
              [Conv.arg1_conv(NatRing.norm_full),
             Conv.arg_conv(Conv.arg1_conv(NatRing.norm_full)),
             Conv.all_conv])))) ctxt)
    ) 


  (***********************************)
  (*         Time Frame Inference   *)
  (***********************************)

  fun print_tac' ctxt i st =
    let val _ = tracing ("..>");
        val _ = tracing (Thm.string_of_thm ctxt st)
    in all_tac st end

  fun time_frame_inference_tac ctxt =
    TRY o resolve_tac ctxt @{thms timeframe_inference_init_normalize}
    THEN' 
    resolve_tac ctxt @{thms timeframe_inference_init} 
    (* normal frame inference *)
    THEN' match_frame_tac (resolve_tac ctxt @{thms ent_refl}) ctxt

    THEN' (resolve_tac ctxt @{thms frame_inference_finalize})
      (* possible non determinism here, countered by the
        application of safe at the end *)
    (*THEN' (fn k => print_tac ctxt "aaa")*)
    THEN'  TRY o (EqSubst.eqsubst_tac ctxt [0] @{thms One_nat_def[symmetric]} ) 
    THEN'  TRY o (REPEAT_DETERM' (EqSubst.eqsubst_tac ctxt [0] @{thms Suc_eq_plus1} )) 

    THEN' (resolve_tac ctxt @{thms TI_QUERYD}) 

    THEN' normalize_time_goal ctxt  

    THEN' split_nat_tac ctxt
   
    THEN' FIRST' [resolve_tac ctxt @{thms refl} ,
        TRY o (safe_steps_tac ctxt) THEN' resolve_tac ctxt @{thms refl}  ]

    ;


  (***********************************)
  (*       Entailment Solver         *)
  (***********************************)

  (* Extract existential quantifiers from entailment goal *)
  fun extract_ex_tac ctxt i st = let
    fun count_ex (Const (@{const_name SLTC.entails},_)$_$c) = 
      count_ex c RS @{thm HOL.mp}
    | count_ex (Const (@{const_name SLTC.ex_assn},_)$Abs (_,_,t))
      = count_ex t RS @{thm enorm_exI'}
    | count_ex _ = @{thm imp_refl};

    val concl = Logic.concl_of_goal (Thm.prop_of st) i |> HOLogic.dest_Trueprop;
    val thm = count_ex concl;
    (* val _ = tracing (Thm.string_of_thm ctxt thm); *)
  in
    (TRY o REPEAT_ALL_NEW (match_tac ctxt @{thms ent_ex_preI}) THEN'
     resolve_tac ctxt [thm]) i st
  end;
 

  fun atom_solve_tac ctxt = 
        FIRST' [ resolve_tac ctxt @{thms ent_refl},
                 SOLVED' ( resolve_tac ctxt @{thms dollarD} THEN'
                             (SELECT_GOAL (auto_tac ctxt))  )
               ]  

  (* Solve Entailment *)
  fun solve_entails_tac ctxt = let
    val preprocess_entails_tac = 
      dflt_tac ctxt 
      THEN' extract_ex_tac ctxt
      THEN' simp_tac 
        (put_simpset HOL_ss ctxt addsimps @{thms solve_ent_preprocess_simps});

    val match_entails_tac =
      FIRST' [

      resolve_tac ctxt @{thms entails_solve_init_time} 
      THEN' match_frame_tac (atom_solve_tac ctxt)  ctxt
      THEN' resolve_tac ctxt @{thms entails_solve_finalize} 
      THEN'  TRY o (EqSubst.eqsubst_tac ctxt [0] @{thms One_nat_def[symmetric]} ) 
      THEN'  TRY o (REPEAT_DETERM' (EqSubst.eqsubst_tac ctxt [0] @{thms Suc_eq_plus1} )) 

      THEN' (resolve_tac ctxt @{thms TI_QUERYD})
      THEN' normalize_time_goal ctxt  
      THEN' SOLVED' (split_nat_tac ctxt),
    
      resolve_tac ctxt @{thms entails_solve_init} 
      THEN' match_frame_tac (atom_solve_tac ctxt)  ctxt
      THEN' resolve_tac ctxt @{thms entails_solve_finalize}
       ];
  in
    preprocess_entails_tac
    THEN' (TRY o
      REPEAT_ALL_NEW (match_tac ctxt (rev (Named_Theorems.get ctxt @{named_theorems sep_eintros}))))
    THEN_ALL_NEW (  dflt_tac ctxt THEN'                                             
      TRY o (match_tac ctxt @{thms ent_triv} 
        ORELSE' resolve_tac ctxt @{thms ent_refl}
        ORELSE' match_entails_tac))
  end;


  (***********************************)
  (* Verification Condition Generator*)
  (***********************************)

  fun heap_rule_tac ctxt h_thms =  
    resolve_tac ctxt h_thms ORELSE' (
    resolve_tac ctxt @{thms fi_rule} THEN' (resolve_tac ctxt h_thms THEN_IGNORE_NEWGOALS
    ( dflt_tac ctxt (*THEN' (fn k => print_tac ctxt "AAAH")*) THEN'  time_frame_inference_tac ctxt) ))                                           

  (* Apply consequence rule if postcondition is not a schematic var *)
  fun app_post_cons_tac ctxt i st = 
    case Logic.concl_of_goal (Thm.prop_of st) i |> HOLogic.dest_Trueprop of
      Const (@{const_name hoare_triple},_)$_$_$qt =>
        if is_Var (head_of qt) then no_tac st
        else resolve_tac ctxt @{thms cons_post_rule} i st
    | _ => no_tac st;

  fun vcg_step_tac ctxt = let
    val h_thms = rev (Named_Theorems.get ctxt @{named_theorems sep_heap_rules});
    val d_thms = rev (Named_Theorems.get ctxt @{named_theorems sep_decon_rules});
    val heap_rule_tac = heap_rule_tac ctxt h_thms

  in
    CSUBGOAL (snd #> (FIRST' [
      CHANGED o dflt_tac ctxt,
      REPEAT_ALL_NEW (resolve_tac ctxt @{thms normalize_rules}),
      CHANGED o (FIRST' [resolve_tac ctxt d_thms, heap_rule_tac]
        ORELSE' (app_post_cons_tac ctxt THEN' 
          FIRST' [resolve_tac ctxt d_thms, heap_rule_tac])) 
    ]))
  end; 
  fun vcg_tac ctxt = REPEAT_DETERM' (  vcg_step_tac ctxt)
                                          
 

  (***********************************)
  (*        Automatic Solver         *)
  (***********************************)

  fun sep_autosolve_tac do_pre do_post ctxt = let
    val pre_tacs = [
      CHANGED o (clarsimp_tac ctxt),
      CHANGED o (REPEAT_ALL_NEW (match_tac ctxt @{thms ballI allI impI conjI}))
    ];                                
    val main_tacs = [
      match_tac ctxt @{thms is_hoare_triple} THEN' CHANGED o vcg_tac ctxt,
      match_tac ctxt @{thms is_entails} THEN' CHANGED o solve_entails_tac ctxt
    ];                                                       
    val post_tacs = [   SELECT_GOAL (auto_tac ctxt)];
    val tacs = (if do_pre then pre_tacs else [])
      @ main_tacs 
      @ (if do_post then post_tacs else []);
  in
    REPEAT_DETERM' (CHANGED o FIRST' tacs)
  end;

  fun sep_step_autosolve_tac do_pre do_post ctxt = let
    val pre_tacs = [
      CHANGED o (clarsimp_tac ctxt),
      CHANGED o (REPEAT_ALL_NEW (match_tac ctxt @{thms ballI allI impI conjI}))
    ];                                
    val main_tacs = [
      match_tac ctxt @{thms is_hoare_triple} THEN' CHANGED o vcg_step_tac ctxt,
      match_tac ctxt @{thms is_entails} THEN' CHANGED o solve_entails_tac ctxt
    ];                                                       
    val post_tacs = [   SELECT_GOAL (auto_tac ctxt)];
    val tacs = (if do_pre then pre_tacs else [])
      @ main_tacs 
      @ (if do_post then post_tacs else []);
  in
      (CHANGED o FIRST' tacs)
  end;

 


end; \<open>struct\<close>


\<close>  

method_setup vcg = \<open>
  Scan.lift (Args.mode "ss") --
  Method.sections Seplogic_Auto.vcg_modifiers >>
  (fn (ss,_) => fn ctxt => SIMPLE_METHOD' (
  CHANGED o (
    if ss then Seplogic_Auto.vcg_step_tac ctxt 
    else Seplogic_Auto.vcg_tac ctxt
  )
))\<close> "Seplogic: Verification Condition Generator"

method_setup sep_auto = 
  \<open>Scan.lift (Args.mode "nopre" -- Args.mode "nopost" -- Args.mode "plain") 
      --| Method.sections Seplogic_Auto.sep_auto_modifiers >>
  (fn ((nopre,nopost),plain) => fn ctxt => SIMPLE_METHOD' (
    CHANGED o Seplogic_Auto.sep_autosolve_tac 
      ((not nopre) andalso (not plain)) 
      ((not nopost) andalso (not plain)) ctxt
  ))\<close> "Seplogic: Automatic solver"

method_setup sep_auto_step = 
  \<open>Scan.lift (Args.mode "nopre" -- Args.mode "nopost" -- Args.mode "plain") 
      --| Method.sections Seplogic_Auto.sep_auto_modifiers >>
  (fn ((nopre,nopost),plain) => fn ctxt => SIMPLE_METHOD' (
    CHANGED o Seplogic_Auto.sep_step_autosolve_tac 
      ((not nopre) andalso (not plain)) 
      ((not nopost) andalso (not plain)) ctxt
  ))\<close> "Seplogic: Automatic solver"

method_setup solve_entails = \<open>
  Method.sections Seplogic_Auto.solve_entails_modifiers >>
  (fn _ => fn ctxt => SIMPLE_METHOD' (
  CHANGED o Seplogic_Auto.solve_entails_tac ctxt
))\<close> "Seplogic: Entailment Solver"

method_setup time_frame_inference = \<open>
  Method.sections Seplogic_Auto.solve_entails_modifiers >>
  (fn _ => fn ctxt => SIMPLE_METHOD' (
  CHANGED o Seplogic_Auto.time_frame_inference_tac ctxt
))\<close> "Seplogic: Frame Inference with Time Inference"
 
method_setup frame_inference = \<open> 
  Method.sections Seplogic_Auto.solve_entails_modifiers >>
  (fn _ => fn ctxt => SIMPLE_METHOD' (
  CHANGED o Seplogic_Auto.frame_inference_tac ctxt
)) \<close> "Seplogic: Frame Inference without Time Inference"

simproc_setup assn_simproc 
  ( "h \<Turnstile> P" | "P\<Longrightarrow>\<^sub>AQ" | "P\<Longrightarrow>\<^sub>tQ" | "(P::assn) = Q" ) 
  = \<open>K Seplogic_Auto.assn_simproc_fun\<close>


subsection \<open>Examples and Regression Tests\<close>

lemma " P * $ 0 \<Longrightarrow>\<^sub>A P * true "
  by (solve_entails)

lemma " P * $ 1 \<Longrightarrow>\<^sub>A P * true * $ 1"
  by (solve_entails)

lemma "QA \<Longrightarrow> (P \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. Q x)"
      apply(tactic \<open>IF_EXGOAL (Seplogic_Auto.extract_ex_tac @{context}) 1\<close>)
  oops

  thm new_rule
schematic_goal "\<And>x. P \<Longrightarrow> Q \<Longrightarrow>   <x \<mapsto>\<^sub>a [0..<n] * $ (n * 15 + 11)> Array_Time.new n 0 <?Q18 x>"
  by (sep_auto heap: new_rule)


lemma "\<And>x. x \<mapsto>\<^sub>a replicate (N * M) 0 * timeCredit_assn ((M * N * 9))  * timeCredit_assn (2) \<Longrightarrow>\<^sub>A x \<mapsto>\<^sub>a replicate (N * M) 0 * timeCredit_assn (Suc (Suc (9 * (N * M))))"
  by (solve_entails)


schematic_goal "\<And>end start' start_next x' k k_next start'a start_nexta x'a enda start'b start_nextb x'b ka k_nexta start'c start_nextc x'c.
       start_nextc = Some p' \<and>
       k_nexta = enda \<and> k_nexta = Some start'c \<and> p' = start'b \<and> start_nexta = Some q' \<and> k_next = end \<and> k_next = Some start'a \<and> q' = start' \<Longrightarrow>
       <start'b \<mapsto>\<^sub>r Cell x'b start_nextb enda * R a x'b *
        (dll_seg R cs' start_nextb (Some start'b) ka enda *  
        (start' \<mapsto>\<^sub>r Cell x' start_next end * R u x' * (dll_seg R vs' start_next (Some start') k end * (start'a \<mapsto>\<^sub>r Cell x'a (Some start') k * R w x'a)))) *
        $ 1>
       !start'b <?Q20 end start' start_next x' k end start'a (Some start') x'a enda start'b start_nextb x'b ka enda start'c (Some start'b) x'c>"
  apply (vcg (ss) heap: lookup_rule) oops

declare entt_refl' [simp]

lemma "\<And>x. M = 0 \<Longrightarrow> (\<And>j i. c (i, j) = 0) \<Longrightarrow> x \<mapsto>\<^sub>a [] \<Longrightarrow>\<^sub>A \<exists>\<^sub>Al. x \<mapsto>\<^sub>a l * true * \<up> (l = []) "
  apply(sep_auto)  
  done



schematic_goal "timeCredit_assn (B* A * 10 + 3) \<Longrightarrow>\<^sub>A ?F1 * timeCredit_assn (B* A + 1)"
  by time_frame_inference  
 
schematic_goal "ya \<mapsto>\<^sub>r Cell x' (Some end) (Some end) * (R x x' * end \<mapsto>\<^sub>r Cell y' (Some ya) (Some ya) * R y y') * $ 9 \<Longrightarrow>\<^sub>A
        ?F62 end x' y' (Cell x' (Some end) (Some end)) ya * $ 1"
  by time_frame_inference  

schematic_goal "\<And>end x' y' xa ya.
       p = Some ya \<Longrightarrow>
       xa = Cell x' (Some end) (Some end) \<Longrightarrow>
       Some ya \<noteq> Some end \<Longrightarrow>
       ya \<mapsto>\<^sub>r Cell x' (Some end) (Some end) * (R x x' * end \<mapsto>\<^sub>r Cell y' (Some ya) (Some ya) * R y y') * $ 9 \<Longrightarrow>\<^sub>A
       ?F62 end x' y' (Cell x' (Some end) (Some end)) ya * $ 1"
  apply time_frame_inference done


(* timeframeinf can solve problems of that form: A * $T \<Longrightarrow>\<^sub>A B * ?F * $T' *)
schematic_goal "\<up> (i < length xs) * a \<mapsto>\<^sub>a xs *  $2  \<Longrightarrow>\<^sub>A a \<mapsto>\<^sub>a xs * ?F * $1"  
  by time_frame_inference

schematic_goal "A * C * $2  \<Longrightarrow>\<^sub>A A * ?F * $1"  
  by time_frame_inference

schematic_goal "a \<mapsto>\<^sub>a xs * $ 1 \<Longrightarrow>\<^sub>A a \<mapsto>\<^sub>a xs * ?F24 (xs ! i)   * $ 1"  
  by time_frame_inference 
thm mult_1

schematic_goal "a \<mapsto>\<^sub>a xs * $ (2 + 3 * ff + (5 * (3*ff+2)))
           \<Longrightarrow>\<^sub>A a \<mapsto>\<^sub>a xs * ?F24   * $ (1 + ff * 2 + 4 * ff)"  
  by time_frame_inference 


context begin
  definition "fffa = (10::nat)"
 
lemma "F * $(xx*(3+7+yy)) \<Longrightarrow>\<^sub>A F * $(xx*2+yy*xx) * true"
  by (solve_entails) 
  

  schematic_goal "(3::nat) + 3 * fffa + 6 * 7 = 1 + ?F"
    apply(tactic \<open>Seplogic_Auto.split_nat_tac @{context} 1\<close>)
    done
  
  schematic_goal "(2::nat) + 3 * fffa  = 1 + ?F"
    apply(tactic \<open>Seplogic_Auto.split_nat_tac @{context} 1\<close>)
    done

  schematic_goal "(2::nat) + fffa * 32 = 1 + fffa * 1 + ?F"
    apply(tactic \<open>Seplogic_Auto.normalize_time_goal @{context} 1\<close>)
    apply(tactic \<open>Seplogic_Auto.split_nat_tac @{context} 1\<close>)
    done

  schematic_goal "(2::nat) + 3 * fffa  = 1 + 2 * fffa + ?F"
    apply(tactic \<open>Seplogic_Auto.normalize_time_goal @{context} 1\<close>)
    apply(tactic \<open>Seplogic_Auto.split_nat_tac @{context} 1\<close>)
    done
end 



lemma "A \<Longrightarrow>\<^sub>A A"
  by solve_entails


lemma "A * B \<Longrightarrow>\<^sub>A A * true"
  by solve_entails  

lemma "A * B * C \<Longrightarrow>\<^sub>A B * A * true"
  by solve_entails





lemma "$a * $b = $(a+b)"  
  by (simp add: time_credit_add)

lemma "$1* \<up>g * G * $2 * $3 *true * F * true * \<up>ff * $4 * $5 = G * F * true * $ 10 * (\<up> g *  $5 * \<up> ff)"
  by (simp add : time_credit_add[symmetric] )  

lemma "G * \<up>ff * true *  F   = H"  apply (simp )   oops

lemma "h \<Turnstile> F \<and>\<^sub>A \<up> (a' = None) * F' \<Longrightarrow> G" apply simp oops

lemma "h \<Turnstile> \<up>t * (F \<and>\<^sub>A \<up> (a' = None) * F') * X \<Longrightarrow> G" apply (simp del:  ) oops


lemma p_c[simp]: "\<up> P * \<up> Q = \<up> (P \<and> Q)" using pure_conj by simp

lemma "\<up>a * B * \<up>c \<Longrightarrow>\<^sub>A G" apply (simp add:  del: pure_conj) oops


lemma "\<exists>\<^sub>Ab. \<up> ((b, a) \<in> R) *C *\<up>a \<Longrightarrow>\<^sub>A emp" apply simp oops


lemma "P * $4 \<Longrightarrow>\<^sub>A P * true * $3"
    "P * $3 \<Longrightarrow>\<^sub>A P * true"
    "P * Q *  $(f x * 4 + 3) \<Longrightarrow>\<^sub>A Q * P * true * $(f x * 4)"
    "P * Q *  $(g y * 6 + f x * 4 + 3) \<Longrightarrow>\<^sub>A Q * P * true * $(g y * 2 + f x * 4)"
  by solve_entails+


lemma "\<And>x. x \<mapsto>\<^sub>a replicate (N * M) 0 * $ ((M * N * 9))  * $ (2)
       \<Longrightarrow>\<^sub>A x \<mapsto>\<^sub>a replicate (N * M) 0 * $ (Suc (Suc (9 * (N * M))))"
  by (sep_auto) 


lemma "\<And>x. x \<mapsto>\<^sub>a replicate (N * M) 0 * $ ((M * N * 9))  * $ (2)
         \<Longrightarrow>\<^sub>A x \<mapsto>\<^sub>a replicate (N * M) 0 * timeCredit_assn (Suc (Suc (9 * (N * M))))"
  apply(vcg (ss))
  by (sep_auto)


subsection \<open>setup sep_auto rules\<close>

thm sep_eintros

lemma ureturn_rule: "<P> ureturn x <\<lambda>r. P * \<up>(r = x)>" 
  apply(rule post_rule)
  apply(rule pre_rule[rotated])
    apply(rule frame_rule[OF return_rule, where R=P] )
  by auto

(* sep auto expects pure assertions to be pulled out in the pre condition TODO: is this correct? *)
lemma nth_rule'[sep_heap_rules]:
  "(i < length xs) \<Longrightarrow> <a \<mapsto>\<^sub>a xs * $ 1 > Array_Time.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up> (r = xs ! i)>"
  apply(rule pre_rule[OF _ nth_rule]) by sep_auto

lemma upd_rule': "i < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs * timeCredit_assn 1 > Array_Time.upd i x a <\<lambda>r. a \<mapsto>\<^sub>a xs[i := x] * \<up> (r = a)>"
  apply(rule pre_rule[OF _ upd_rule])  
  by solve_entails

lemma assert_rule_alt: 
  "(Q \<Longrightarrow>\<^sub>A true * \<up>(P x)) \<Longrightarrow>
     <Q * $1> assert P x <\<lambda> _. Q * \<up>(P x)>"
  unfolding assert_def
  apply (sep_auto heap: SLTC.return_rule decon: assert_rule)
  unfolding hoare_triple_def
  using mod_starD by blast



lemma option_rule:
  assumes "p = None \<Longrightarrow> <P> f <Q>"
  assumes "\<And> x. p = Some x \<Longrightarrow> <P> g x <Q>"
  shows "<P> case p of None \<Rightarrow> f | Some x \<Rightarrow> g x <Q>"
  using assms by (sep_auto split: option.splits)

lemma prod_rule:
  assumes "\<And> x y. z = (x, y) \<Longrightarrow> <P> g x y <Q>"
  shows "<P> case z of (x, y) \<Rightarrow> g x y <Q>"
  using assms by (sep_auto split: prod.splits)

lemma prod_pre_split: 
  assumes "\<And> x y. <P x y * \<up> (p = (x, y))> f <Q>"
  shows "<case p of (x, y) \<Rightarrow> P x y> f <Q>"
proof (cases p)
  case [simp]: (Pair x y)
  have "P x y * \<up> (p = (x, y)) = (case p of (x, y) \<Rightarrow> P x y)" by simp
  then show ?thesis using assms[of x y] by simp
qed

lemmas prod_split_rule = prod_rule


lemma If_rule:
  "(b \<Longrightarrow> <P> f <Q>) \<Longrightarrow> (\<not> b \<Longrightarrow> <P> g <Q>) \<Longrightarrow> <P> if b then f else g <Q>"
  by auto 

lemma Let_rule: "(\<And>x. x = t \<Longrightarrow> <P> f x <Q>) \<Longrightarrow> <P> Let t f <Q>" 
  by simp


lemma prod_case_simp[sep_dflt_simps]:
  "(case (a, b) of (c, d) \<Rightarrow> f c d) = f a b" by simp


lemmas [sep_decon_rules] = 
          assert_rule bind_rule ureturn_rule Let_rule If_rule
          option_rule prod_rule prod_pre_split
                 
lemmas [sep_heap_rules] =
          length_rule SLTC.return_rule
          new_rule make_rule
          ref_rule lookup_rule upd_rule'
          update_rule 
          assert_rule_alt


thm upd_rule'

lemmas [sep_eintros] = impI conjI exI
   
subsection \<open>examples for sep_auto\<close>
      
schematic_goal "<$ 1> Array_Time.new 0 0 <?Q8>"
  by sep_auto


subsection \<open>BUGS and Ideas for enhancements\<close>

text \<open>time_frame_inference has the invariant, that the last
    component in the symbolic heap is a time credit.
    once such a time credit is not available the method breaks,
    this occurs for example, when an operation has no advertised cost
    while using sep_auto.
    e.g. in fibonacci/Doubly_Linked_List_With_Time : dll_fold_rule_weak\<close>
schematic_goal " xs\<^sub>2 = [] \<Longrightarrow>
          A * (B * F) * $ (Suc (Suc 0)) \<Longrightarrow>\<^sub>A
          B * F * ?R * $0" 
  apply time_frame_inference oops

schematic_goal " xs\<^sub>2 = [] \<Longrightarrow>
          A * (B * F) * $ (Suc (Suc 0)) \<Longrightarrow>\<^sub>A
          B * F * ?R "   oops



end
