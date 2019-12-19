theory Transpile
imports "SepAuto_Time" 
    "Separation_Logic_Imperative_HOL.Hoare_Triple"  
  "SeprefTime.Term_Synth" "Monad_Memo_DP.Transform_Cmd"
  "SeprefTime.Pf_Mono_Prover"
  "SeprefTime.Refine_Automation"
  keywords  
    "transpile_define" :: thy_decl and
    "transpile_replay" :: thy_decl and
    "transpile_prove" :: thy_decl  
begin


section \<open>Misc\<close>

subsection \<open>Imperative-HOL\<close>

lemma run_to_execute':
  "Run.run c (Some h) \<sigma>' r  \<Longrightarrow> if \<sigma>' = None then execute c h = None else execute c h = Some (r, the \<sigma>')" 
  apply(induct arbitrary:     rule: Run.run.cases )
  by auto

lemma run_and_execute: "(\<forall>\<sigma> r. run c (Some h) \<sigma> r  \<longrightarrow> \<sigma> \<noteq> None \<and> P (the \<sigma>) r )
        \<longleftrightarrow> (\<exists>h' r. execute c h = Some (r, h') \<and> P h' r)"  
  apply rule
  subgoal  
    by (metis Heap_Monad.effect_def effect_run is_exn.simps(1) new_exn not_Some_eq2 option.sel the_state.simps)
   (*  by (metis option.sel run.intros(2) run.intros(3) ) *)
  subgoal by (metis (mono_tags) not_None_eq option.sel prod.sel(1) prod.sel(2) run_to_execute') 
  done
  


lemma not_is_exn_conv: "\<not> is_exn \<sigma> \<longleftrightarrow> \<sigma> \<noteq> None" apply(cases \<sigma>) by auto

lemma hoare_triple_execute: 
  "Hoare_Triple.hoare_triple P  c Q = (\<forall>h as.
        (h,as) \<Turnstile> P \<longrightarrow> (\<exists>h'  r. Heap_Monad.execute c h = Some (r, h') \<and>
        (h', Hoare_Triple.new_addrs h as h') \<Turnstile> Q r \<and>
          Assertions.relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'))" (is "?L = (\<forall>h as . ?H h as   \<longrightarrow> (\<exists>h' r. _ \<and> ?P h as h'   r))")
proof -
  have **: "\<And>x. x \<noteq> None \<Longrightarrow>  the_state x = the x"
      by(auto  )
  have *: "\<And>h P. (\<forall>\<sigma> r. run c (Some h) \<sigma> r  \<longrightarrow> \<sigma> \<noteq> None \<and> P (the_state \<sigma>) r ) =
    (\<forall>\<sigma> r. run c (Some h) \<sigma> r  \<longrightarrow> \<sigma> \<noteq> None \<and> P (the \<sigma>) r ) "
    using ** by metis 

  have "?L = (\<forall>h as . (h,as) \<Turnstile> P \<longrightarrow> 
                  (\<forall> \<sigma> r. Run.run c (Some h) \<sigma> r  \<longrightarrow> \<sigma> \<noteq> None \<and> (?P h as (the_state \<sigma>)    r)))"
    unfolding Hoare_Triple.hoare_triple_def Let_def not_is_exn_conv  by auto
  also have "\<dots> =  (\<forall>h as . (h,as) \<Turnstile> P \<longrightarrow>
              (\<exists>h'  r. Heap_Monad.execute c h = Some (r, h' ) \<and>
                         ?P h as h'   r))"
    apply(subst *)  
    apply(subst run_and_execute)
    by simp
  finally show ?thesis .
qed


subsection \<open>Imperative-HOL with time\<close>

lemma run_and_executeT: "(\<forall>\<sigma> t r. SepAuto_Time.run c (Some h) \<sigma> r t \<longrightarrow> \<sigma> \<noteq> None \<and> P (the \<sigma>) r t)
        \<longleftrightarrow> (\<exists>h' t r. Heap_Time_Monad.execute c h = Some (r, h', t) \<and> P h' r t)"  
  apply rule
  subgoal by (metis option.sel SepAuto_Time.run.intros(2) SepAuto_Time.run.intros(3) timeFrame.elims) 
  subgoal by (metis (mono_tags) not_None_eq option.sel prod.sel(1) prod.sel(2) run_to_execute) 
  done


lemma hoare_tripleT_execute: 
  "SepAuto_Time.hoare_triple P  c Q = (\<forall>h as n.
        pHeap h as n \<Turnstile> P \<longrightarrow> (\<exists>h' t r. Heap_Time_Monad.execute c h = Some (r, h', t) \<and>
        (pHeap h' (SepAuto_Time.new_addrs h as h') (n - t) \<Turnstile> Q r \<and>
        t \<le> n \<and> SepAuto_Time.relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')))" (is "?L = (\<forall>h as n. ?H h as n \<longrightarrow> (\<exists>h' t r. _ \<and> ?P h as h' n t r))")
proof -
  have "?L = (\<forall>h as n. pHeap h as n \<Turnstile> P \<longrightarrow> 
                  (\<forall> \<sigma> t r. SepAuto_Time.run c (Some h) \<sigma> r t \<longrightarrow> \<sigma> \<noteq> None \<and> (?P h as (the \<sigma>) n t r)))"
    unfolding SepAuto_Time.hoare_triple_def by auto
  also have "\<dots> =  (\<forall>h as n. pHeap h as n \<Turnstile> P \<longrightarrow>
              (\<exists>h' t r. Heap_Time_Monad.execute c h = Some (r, h', t) \<and>
                         ?P h as h' n t r))" apply(subst run_and_executeT) by simp
  finally show ?thesis .
qed

lemma hoare_tripleT_executeD: 
  "SepAuto_Time.hoare_triple P  c Q \<Longrightarrow> (\<And>h as n.
        pHeap h as n \<Turnstile> P \<Longrightarrow> (\<exists>h' t r. Heap_Time_Monad.execute c h = Some (r, h', t) \<and>
        (pHeap h' (SepAuto_Time.new_addrs h as h') (n - t) \<Turnstile> Q r \<and>
        t \<le> n \<and> SepAuto_Time.relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h')))" 
  using hoare_tripleT_execute by blast




section \<open>Relation between Imperative-HOL and Imperative-HOL with time\<close>

lemma relH_eq: "Assertions.relH =  SepAuto_Time.relH"
  unfolding  SepAuto_Time.relH_def Assertions.relH_def
  apply(rule ext)+ apply auto using Assertions.in_range.simps by blast+   


lemma new_addrs_eq: "Hoare_Triple.new_addrs =  SepAuto_Time.new_addrs"
  unfolding Hoare_Triple.new_addrs_def SepAuto_Time.new_addrs_def  ..

lemma aseval_assn_fn_conv: "aseval = assn_fn"
  apply (rule ext) apply(rule ext)   
  by (metis aseval.simps assn_raw.collapse)  

lemma Array_set_conv: "Array_Time.set h a = Array.set h a" 
  unfolding Array_Time.length_def Array.length_def Array.set_def Array_Time.set_def by simp

lemma Array_get_conv: "Array_Time.get h a = Array.get h a"
  unfolding Array_Time.length_def Array.length_def Array.get_def Array_Time.get_def by simp

lemma Array_update_conv: "Array_Time.update a i x h = Array.update  a i x h"
  unfolding Array_Time.update_def Array.update_def  by (simp add: Array_set_conv Array_get_conv)

lemma Array_alloc_conv: "Array_Time.alloc xs h = Array.alloc xs h"
  unfolding Array_Time.alloc_def Array.alloc_def Array_set_conv by simp

lemma Array_length_conv: "Array_Time.length h a = Array.length h a"
  unfolding Array_Time.length_def Array.length_def Array_get_conv by simp


lemma Ref_set_conv: "Ref_Time.set r x = Ref.set r x"
  unfolding Ref_Time.set_def Ref.set_def by simp

lemma Ref_get_conv: "Ref_Time.get r x = Ref.get r x"
  unfolding Ref_Time.get_def Ref.get_def by simp

lemma Ref_alloc_conv: "Ref_Time.alloc x h = Ref.alloc x h"
  unfolding Ref_Time.alloc_def Ref.alloc_def by (simp add: Ref_set_conv)

subsection \<open>forget\<close>

named_theorems_rev forget_it
      "Rules for flattening assertions of Imperative-HOL with time"

abbreviation (input) forget :: "(SepAuto_Time.assn) \<Rightarrow> Assertions.assn"
  where "forget P \<equiv> Assertions.Abs_assn (\<lambda>(h,addrs). \<exists>t. (assn_fn (SepAuto_Time.Rep_assn P)) (pHeap h addrs t))"

lemma models_forget_modelsT: "(h, as) \<Turnstile> forget P \<Longrightarrow> \<exists>n. pHeap h as n \<Turnstile> P"
   unfolding SepAuto_Time.models_def
   apply(subst (asm) Abs_assn_inverse)
   subgoal apply (auto simp: proper_def)  
      apply (metis Assertions.in_range.simps SepAuto_Time.in_range.simps SepAuto_Time.models_in_range aseval.simps assn_raw.exhaust_sel models_def)
      
     by (metis SepAuto_Time.mod_relH aseval.simps assn_raw.exhaust_sel models_def relH_eq)  
   subgoal apply auto unfolding aseval_assn_fn_conv by blast
   done

lemma modelsT_forget_models: " pHeap h' as t \<Turnstile> P \<Longrightarrow> (h', as) \<Turnstile> forget P"
   unfolding SepAuto_Time.models_def 
   apply(subst  Abs_assn_inverse)
   subgoal  apply (auto simp: proper_def) 
     subgoal 
       by (metis Assertions.in_range.simps SepAuto_Time.in_range.simps SepAuto_Time.proper_def aseval_assn_fn_conv proper_Rep_assn)
     subgoal 
       by (metis SepAuto_Time.proper_def aseval_assn_fn_conv proper_Rep_assn relH_D relH_eq) 
     done
   by (auto simp: aseval_assn_fn_conv) 

 subsection \<open>syntax directed rules for @{term forget}\<close>


lemma assn_fn_models_conv: "assn_fn (SepAuto_Time.assn.Rep_assn A) (pHeap x y t) 
      \<longleftrightarrow> (pHeap x y t) \<Turnstile> A"   
  by (simp add: models_def aseval_assn_fn_conv)

lemma forget_dollar[forget_it]: 
  "forget ($n) = emp"
    unfolding timeCredit_assn_def
    unfolding one_assn_def  
     apply(subst   SepAuto_Time.Abs_assn_inverse   )
    subgoal apply auto
      unfolding SepAuto_Time.proper_def by auto 
    apply(rule arg_cong[where f=Assertions.assn.Abs_assn])
    apply(rule ext) by auto 

lemma  forget_star[forget_it]:
  "forget (A * B) = forget A * forget B"
  apply (rule  ) apply rule
  subgoal for h unfolding mod_star_conv
    apply safe
    unfolding assn_fn_models_conv
    apply(drule SepAuto_Time.mod_star_convE)
    apply auto
    subgoal  for x as1 as2 n1 n2
      apply(rule exI[where x=as1])
      apply(rule exI[where x=as2]) apply auto
      subgoal                           
        apply(subst   Abs_assn_inverse  )
        subgoal apply (auto simp: Assertions.proper_def)
          subgoal  
            using Assertions.in_range.simps SepAuto_Time.models_in_range by auto  
          subgoal  
            using SepAuto_Time.mod_relH relH_eq by fastforce   
          done
        apply simp apply(rule exI[where x=n1]) by simp
      subgoal                           
        apply(subst   Abs_assn_inverse  )
        subgoal apply (auto simp: Assertions.proper_def)
          subgoal  
            using Assertions.in_range.simps SepAuto_Time.models_in_range by auto  
          subgoal  
            using SepAuto_Time.mod_relH relH_eq by fastforce   
          done
        apply simp apply(rule exI[where x=n2]) by simp
      done
    done
  subgoal for h unfolding mod_star_conv assn_fn_models_conv 
    apply(subst  (asm) Abs_assn_inverse  )
    subgoal apply (auto simp: Assertions.proper_def)
      subgoal  
        using Assertions.in_range.simps SepAuto_Time.models_in_range by auto  
      subgoal  
        using SepAuto_Time.mod_relH relH_eq by fastforce   
      done
    apply(subst  (asm) Abs_assn_inverse  )
    subgoal apply (auto simp: Assertions.proper_def)
      subgoal  
        using Assertions.in_range.simps SepAuto_Time.models_in_range by auto  
      subgoal  
        using SepAuto_Time.mod_relH relH_eq by fastforce   
      done
    apply auto
    subgoal for hr as1 as2 t ta
      apply(rule exI[where x="t+ta"])
      apply(rule SepAuto_Time.mod_star_convI)
      by auto
    done
  done

lemma forget_other[forget_it]:
  "forget true = true"
  "forget (\<up>P) = \<up>P"
  "forget false = false"
  "forget (p \<mapsto>\<^sub>a xs) = p \<mapsto>\<^sub>a xs"
  "forget (q \<mapsto>\<^sub>r v) = q \<mapsto>\<^sub>r v"
  subgoal   
    apply rule
    apply rule
    subgoal for h  
      using Assertions.in_range.simps assn_fn_models_conv top_assn_rule by auto  
    subgoal for h
      apply safe
      apply(rule exI[where x=0])       
      by (simp add: Assertions.in_range.simps assn_fn_models_conv top_assn_rule) 
    done
  subgoal 
    by(auto intro: Abs_assn_eqI
            simp: SepAuto_Time.pure_assn_def SepAuto_Time.Abs_assn_inverse
                  SepAuto_Time.proper_def )
  subgoal 
    by(auto intro: Abs_assn_eqI
            simp: SepAuto_Time.pure_assn_def SepAuto_Time.Abs_assn_inverse
                  SepAuto_Time.proper_def )
  subgoal apply(rule)
    apply rule 
    subgoal for h unfolding SepAuto_Time.snga_assn_def Assertions.snga_assn_def 
      apply(subst (asm)  SepAuto_Time.Abs_assn_inverse   )
      subgoal by(auto simp: SepAuto_Time.proper_def  SepAuto_Time.relH_array)  
      subgoal by (auto simp add: Array_get_conv Assertions.assn.Abs_assn_inverse) 
      done
    subgoal for h  unfolding SepAuto_Time.snga_assn_def Assertions.snga_assn_def
      apply(subst  SepAuto_Time.Abs_assn_inverse   )
      subgoal by(auto simp: SepAuto_Time.proper_def SepAuto_Time.relH_array) 
      subgoal by (auto simp add: Array_get_conv Assertions.assn.Abs_assn_inverse) 
      done
    done
  subgoal apply(rule)
    apply rule 
    subgoal for h unfolding SepAuto_Time.sngr_assn_def Assertions.sngr_assn_def 
      apply(subst (asm)  SepAuto_Time.Abs_assn_inverse   )
      subgoal by(auto simp: SepAuto_Time.proper_def  SepAuto_Time.relH_ref)  
      subgoal by (auto simp add: Ref_get_conv Assertions.assn.Abs_assn_inverse) 
      done
    subgoal for h  unfolding SepAuto_Time.sngr_assn_def Assertions.sngr_assn_def 
      apply(subst  SepAuto_Time.Abs_assn_inverse   )
      subgoal by(auto simp: SepAuto_Time.proper_def SepAuto_Time.relH_ref) 
      subgoal by (auto simp add: Ref_get_conv Assertions.assn.Abs_assn_inverse) 
      done
    done
  done


lemma forget_ex[forget_it]: "forget (\<exists>\<^sub>A x. P x) = (\<exists>\<^sub>A x. forget (P x))"
  apply rule
  apply rule
  subgoal for h apply safe
    unfolding SepAuto_Time.ex_assn_def 
      apply(subst (asm)  SepAuto_Time.Abs_assn_inverse   )
    subgoal using SepAuto_Time.models_in_range 
        apply (auto simp: SepAuto_Time.proper_def  ) 
      using SepAuto_Time.mod_relH by blast
    apply auto  
    using modelsT_forget_models by blast  
  subgoal for h apply safe
    unfolding SepAuto_Time.ex_assn_def 
      apply(subst   SepAuto_Time.Abs_assn_inverse   )
    subgoal using SepAuto_Time.models_in_range 
        apply (auto simp: SepAuto_Time.proper_def  ) 
      using SepAuto_Time.mod_relH by blast
    apply auto   
    using models_forget_modelsT by blast  
  done
 

subsection \<open>flatten\<close>

definition flatten :: "'a Heap_Time_Monad.Heap \<Rightarrow> 'a Heap_Monad.Heap" where
  "flatten c = (case c of Heap_Time_Monad.Heap p \<Rightarrow> Heap_Monad.Heap
                   (\<lambda>h. case p h of Some x \<Rightarrow> (case x of (r,h,t) \<Rightarrow> Some (r,h)) | None \<Rightarrow> None))"
 
lemma runT_flatten_run: "SepAuto_Time.run c (Some h) \<sigma> r t \<Longrightarrow> Run.run (flatten c) (Some h) \<sigma> r" 
  apply(induct rule: SepAuto_Time.run.induct)
  subgoal apply(rule Run.run.push_exn) by simp
  subgoal for c  apply(rule Run.run.new_exn)
     apply simp apply (simp add: flatten_def)
    apply (cases c)  by simp
  subgoal for c  apply(rule Run.run.regular) apply simp
    apply(cases c) by (simp add: flatten_def)
  done

lemma run_runT_flatten': "Run.run c' (Some h) \<sigma> r \<Longrightarrow> c' = flatten c \<Longrightarrow> \<exists>t. SepAuto_Time.run c (Some h) \<sigma> r t " 
  apply(induct arbitrary: c rule: Run.run.induct)
  subgoal for \<sigma> apply(cases \<sigma>) apply auto apply(rule exI)
    by(rule SepAuto_Time.run.intros(1))  
  subgoal for \<sigma> c r c'   apply(cases \<sigma>) apply auto
    apply(rule exI) apply(rule SepAuto_Time.run.intros(2))      
    apply (cases c') by (auto simp add: flatten_def split: option.splits)
  subgoal for \<sigma> c r h' c' apply(cases \<sigma>) apply auto
    apply(cases c')
    subgoal for h x 
      apply(rule exI[where x="snd (snd (the (x h)))"])
      apply(rule SepAuto_Time.run.intros(3))   by (auto simp add: flatten_def split: option.splits) try0
    done
  done

lemma run_runT_flatten: "Run.run (flatten c) (Some h) \<sigma> r \<Longrightarrow> \<exists>t. SepAuto_Time.run c (Some h) \<sigma> r t"
  using run_runT_flatten' by fast


lemma hoare_tripleT_flatten_hoare_triple: assumes "SepAuto_Time.hoare_triple P c Q"
  shows "Hoare_Triple.hoare_triple (forget P) (flatten c) (\<lambda>r. forget (Q r))"
  unfolding Hoare_Triple.hoare_triple_def Let_def
proof safe
  fix h as \<sigma> r
  assume a: "(h, as) \<Turnstile> forget P" and b: "Run.run (flatten c) (Some h) \<sigma> r"
  
  from a[THEN models_forget_modelsT] obtain n where p: "pHeap h as n \<Turnstile> P " by blast
  from run_runT_flatten[OF b] obtain t where "SepAuto_Time.run c (Some h) \<sigma> r t" by blast
  from assms[THEN SepAuto_Time.hoare_tripleD, OF this] have
    *:  "\<And>as n. pHeap h as n \<Turnstile> P \<Longrightarrow>
     \<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (SepAuto_Time.new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> Q r
     \<and> t \<le> n \<and> SepAuto_Time.relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>) \<and> heap.lim h \<le> heap.lim (the \<sigma>)" by blast

  from *[OF p] have i: "\<sigma> \<noteq> None" "pHeap (the \<sigma>) (SepAuto_Time.new_addrs h as (the \<sigma>)) (n - t) \<Turnstile> Q r"
    "t \<le> n" "SepAuto_Time.relH {a. a < heap.lim h \<and> a \<notin> as} h (the \<sigma>)" "heap.lim h \<le> heap.lim (the \<sigma>)"
    by auto

  show "(the_state \<sigma>, Hoare_Triple.new_addrs h as (the_state \<sigma>)) \<Turnstile> forget (Q r)"
    unfolding new_addrs_eq
    using i(2) apply(intro modelsT_forget_models) using i(1) by force

  show "Assertions.relH {a. a < heap.lim h \<and> a \<notin> as} h (the_state \<sigma>)"
    unfolding relH_eq  using i by force

  show " heap.lim h \<le> heap.lim (the_state \<sigma>)"
    using i by force

  assume "is_exn \<sigma>" then show "False"
    using i(1) by auto
qed



subsection \<open>refines\<close>



definition "refines c' c \<equiv> \<forall> h h' r n.
     Heap_Time_Monad.effect c h h' r n \<longrightarrow> Heap_Monad.effect c' h h' r "

lemma refinesD1:
  assumes "refines c' c "
  shows " \<And>h h' r n. Heap_Time_Monad.effect c h h' r n \<Longrightarrow> Heap_Monad.effect c' h h' r"
  using assms  unfolding refines_def   by auto

lemma refinesI:
  assumes  " \<And>h h' r n. Heap_Time_Monad.effect c h h' r n \<Longrightarrow> Heap_Monad.effect c' h h' r"
  shows "refines c' c "
  using assms  unfolding refines_def   by auto
 

lemma refinesD:
  assumes "refines c' c "
  shows " (\<And>h h' r n. Heap_Time_Monad.execute c h = Some (r, h', n) \<Longrightarrow> Heap_Monad.execute c' h = Some (r, h'))"
  using assms  unfolding refines_def Heap_Monad.effect_def Heap_Time_Monad.effect_def by auto


lemma refines_flatten: "refines (flatten f) f"
  unfolding refines_def Heap_Monad.effect_def Heap_Time_Monad.effect_def 
  using runT_flatten_run SepAuto_Time.run.intros(3) run_to_execute' by fastforce  




lemma refines_HT': assumes "SepAuto_Time.hoare_triple P c Q"
      and R: "refines c' c"
  shows "Hoare_Triple.hoare_triple (forget P) c' (\<lambda>r. forget (Q r))"
  unfolding hoare_triple_execute Let_def
proof safe
  fix h as 
  assume a: "(h, as) \<Turnstile> forget P"   
  from a[THEN models_forget_modelsT] obtain n where p: "pHeap h as n \<Turnstile> P " by blast

  from assms(1)[THEN hoare_tripleT_executeD, OF this] obtain h' t r where
   A :"  Heap_Time_Monad.execute c h = Some (r, h', t) " 
   and B: "pHeap h' (SepAuto_Time.new_addrs h as h') (n - t) \<Turnstile> Q r"
   and C: "t \<le> n" and D: "SepAuto_Time.relH {a. a < heap.lim h \<and> a \<notin> as} h h'"
   and E: "heap.lim h \<le> heap.lim h'" by blast

  from refinesD[OF R A] have "Heap_Monad.execute c' h = Some (r, h')" .


  show "\<exists>h' r.
          Heap_Monad.execute c' h = Some (r, h') \<and>
          (h', Hoare_Triple.new_addrs h as h') \<Turnstile>
          Assertions.assn.Abs_assn (\<lambda>(h, addrs). \<exists>t. assn_fn (SepAuto_Time.assn.Rep_assn (Q r)) (pHeap h addrs t)) \<and>
          Assertions.relH {a. a < heap.lim h \<and> a \<notin> as} h h' \<and> heap.lim h \<le> heap.lim h'"
    apply(rule exI[where x=h'])
    apply(rule exI[where x=r])
  proof safe
    show "Heap_Monad.execute c' h = Some (r, h')" by fact
    show "(h', Hoare_Triple.new_addrs h as h') \<Turnstile> forget (Q r)"
      unfolding new_addrs_eq
      using B apply(intro modelsT_forget_models) using A by force 
    show "Assertions.relH {a. a < heap.lim h \<and> a \<notin> as} h h'"
      unfolding relH_eq  using D by force

    show " heap.lim h \<le> heap.lim h'" by fact
  qed
qed 

lemma refines_HT: assumes "refines c' c" and "SepAuto_Time.hoare_triple P c Q"
  and "P'=forget P" and "Q' = (\<lambda>r. forget (Q r))"
  shows "Hoare_Triple.hoare_triple P' c' Q'"
  using assms refines_HT'  
  by fast



named_theorems_rev transpile_rules
      "Rules for transpiling from Imperative-HOL with time
        to vanilla Imperative-HOL"

subsubsection \<open>refines for combinators\<close>

lemma refines_combinators: 
  "refines m' m \<Longrightarrow> (\<And>v. refines (f' v) (f v)) \<Longrightarrow> refines (m' \<bind> f') (m \<bind> f)"
    "(b \<Longrightarrow> refines x' x) \<Longrightarrow> (~b \<Longrightarrow> refines y' y) \<Longrightarrow> refines (if b then x' else y') (if b then x else y)"
  "refines (return v) (Heap_Time_Monad.return v)"
  "refines (F' n) (F n) \<Longrightarrow> refines (Let n F') (Let n F)" 
  subgoal 
  proof -
    assume "refines m' m"
    then have *: "\<And>h a h' n. Heap_Time_Monad.execute m h = Some (a, h', n)
       \<Longrightarrow> Heap_Monad.execute m' h = Some (a, h')"         
      unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
      by simp

    assume 2: "(\<And>v. refines (f' v) (f v))"
    have ***: "\<And>b h h' n a x.
       timeFrame b (Heap_Time_Monad.execute (f h) x) = Some (a, h', n) 
          \<Longrightarrow> Some (a, h')  = Heap_Monad.execute (f' h) x"
      subgoal for b h h' n a x
          using 2 unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          apply (auto split: option.splits Heap_Time_Monad.Heap.splits)  
          apply(cases "(Heap_Time_Monad.execute (f h) x)")   by (auto split: option.splits)
        done

    show "refines (m' \<bind> f') (m \<bind> f)"
      unfolding refines_def  Heap_Time_Monad.bind_def Heap_Monad.bind_def 
            Heap_Time_Monad.effect_def Heap_Monad.effect_def  
      by(auto simp: *  *** split: option.splits)
  qed
  subgoal unfolding refines_def by auto
  subgoal unfolding refines_def  
    using Heap_Monad.effect_returnI Heap_Time_Monad.effect_returnE  
    by fast 
  subgoal unfolding refines_def by auto
  done 

lemma [transpile_rules]:   "
  (\<And>a b. refines (f' a b) (f a b)) \<Longrightarrow>
  refines (case x of (a,b) \<Rightarrow> f' a b) (case x of (a,b) \<Rightarrow> f a b)"
  by (auto split: prod.splits)

lemma [transpile_rules]:   "refines (return v) (ureturn v)"
  unfolding refines_def return_def ureturn_def
    Heap_Time_Monad.effect_def Heap_Monad.effect_def
    Heap_Time_Monad.heap_def Heap_Monad.heap_def
  by auto

lemma [transpile_rules]: "refines f' f 
  \<Longrightarrow> (\<And>y. refines (g' y) (g y)) \<Longrightarrow> 
refines (case x of None \<Rightarrow> f' | Some y \<Rightarrow> g' y)  (case x of None \<Rightarrow> f | Some y \<Rightarrow> g y)"
  by (auto split: option.splits)

lemma assumes  M: "(\<And>x. Heap_Time_Monad.mono_Heap (\<lambda>f. F f x))" 
    and M2: "\<And>x. Heap_Monad.mono_Heap (\<lambda>f. F' f x)"
and S: "(\<And>f f' x h h' r n.
    (\<And>x h h' r n. Heap_Time_Monad.effect (f x) h h' r n \<Longrightarrow> Heap_Monad.effect (f' x) h h' r) \<Longrightarrow>
    Heap_Time_Monad.effect (F f x) h h' r n \<Longrightarrow> Heap_Monad.effect (F' f' x) h h' r)"
shows effect_fixp:
"\<And>h h' r n x. Heap_Time_Monad.effect (Heap_Time_Monad.heap.fixp_fun F x) h h' r n \<Longrightarrow> Heap_Monad.effect (Heap_Monad.heap.fixp_fun F' x) h h' r"
  apply(rule Heap_Time_Monad.fixp_induct_heap[where U=id and C=id and F=F, simplified,
        where P="\<lambda>x h h' r n. Heap_Monad.effect (Heap_Monad.heap.fixp_fun F' x) h h' r", simplified])

  subgoal apply(rule M ) done
    apply simp defer
   apply simp

  apply (subst heap.mono_body_fixp[OF M2] ) 
  apply(rule S[where f'="(Heap_Monad.heap.fixp_fun F')"])
   apply blast
  apply blast
  done

lemma refines_fixp[transpile_rules]:
  assumes M: "(\<And>x. Heap_Time_Monad.mono_Heap (\<lambda>f. F f x))" 
  assumes  S: "(\<And>f f' x h h' r n.
         (\<And>x. refines (f' x) (f x) ) \<Longrightarrow> refines (F' f' x) (F f x) )"
  assumes M2: "\<And>x. Heap_Monad.mono_Heap (\<lambda>f. F' f x)"
  shows "\<And>h h' r n x. refines
    (Heap_Monad.heap.fixp_fun F' x) (Heap_Time_Monad.heap.fixp_fun F x)"
  using S unfolding refines_def apply safe apply(rule effect_fixp[OF M M2]) by blast+  




subsubsection \<open>Refines for basic operations\<close>




lemma refines_ref_lookup[transpile_rules]: "refines (Ref.lookup r) (Ref_Time.lookup r)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
        Ref_Time.lookup_def Ref.lookup_def
        Heap_Time_Monad.tap_def Heap_Monad.tap_def
        Heap_Time_Monad.heap_def Heap_Monad.heap_def
  by (auto simp: Ref_get_conv )

lemma refines_ref[transpile_rules]: "refines (Ref.ref x) (Ref_Time.ref x)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
        Ref_Time.ref_def Ref.ref_def
        Heap_Time_Monad.heap_def Heap_Monad.heap_def
  by (auto simp: Ref_alloc_conv split: prod.splits)

lemma refines_ref_update[transpile_rules]: "refines (Ref.update r v) (Ref_Time.update r v)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
        Ref_Time.update_def Ref.update_def
        Heap_Time_Monad.heap_def Heap_Monad.heap_def
  by (auto simp: Ref_set_conv )

lemma refines_raise[transpile_rules]:
  "refines (Heap_Monad.raise (String.implode msg)) (Heap_Time_Monad.raise msg)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
        Heap_Time_Monad.raise_def Heap_Monad.raise_def
  by auto

lemma refines_nth:
    "refines (Array.nth a l) (Array_Time.nth a l)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.nth_def  Array.nth_def 
          Heap_Time_Monad.guard_def  Heap_Monad.guard_def
  by (auto simp: Array_length_conv Array_get_conv)


lemma refines_make:
    "refines (Array.make n f) (Array_Time.make n f)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.make_def  Array.make_def 
        Heap_Time_Monad.heap_def Heap_Monad.heap_def
  by (auto simp: Array_length_conv Array_get_conv Array_alloc_conv split: prod.splits) 


lemma refines_freeze:
    "refines (Array.freeze a) (Array_Time.freeze a)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.freeze_def  Array.freeze_def  
        Heap_Time_Monad.heap_def Heap_Monad.heap_def
          Heap_Time_Monad.tap_def  Heap_Monad.tap_def
  by (auto simp: Array_length_conv Array_get_conv)


lemma refines_of_list:
    "refines (Array.of_list xs) (Array_Time.of_list xs)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.of_list_def  Array.of_list_def  
        Heap_Time_Monad.heap_def Heap_Monad.heap_def
          Heap_Time_Monad.tap_def  Heap_Monad.tap_def
  apply (auto simp: Array_length_conv Array_alloc_conv split: option.splits)  
  by (smt Array.alloc_def fst_conv prod.case_eq_if snd_conv)  
 

lemma refines_array_upd:
    "refines (Array.upd i x a) (Array_Time.upd i x a)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.upd_def  Array.upd_def 
          Heap_Time_Monad.guard_def  Heap_Monad.guard_def
  by (auto simp: Array_length_conv Array_update_conv)

lemma refines_array_new:
    "refines (Array.new n x) (Array_Time.new n x)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.new_def  Array.new_def 
          Heap_Time_Monad.guard_def  Heap_Monad.guard_def
        Heap_Time_Monad.heap_def Heap_Monad.heap_def
  apply (auto simp: Array_length_conv Array_alloc_conv split: option.splits)  
  by (smt Array.alloc_def fst_conv prod.case_eq_if snd_conv)  


lemma refines_len:
    "refines (Array.len a) (Array_Time.len a)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.len_def  Array.len_def 
          Heap_Time_Monad.tap_def  Heap_Monad.tap_def
  by (auto simp: Array_length_conv)



lemmas [transpile_rules] = refines_combinators
  refines_nth refines_len refines_array_upd refines_array_new
  refines_freeze refines_of_list refines_make


section \<open>Automating Transpilation\<close>


ML \<open>                      


  datatype tp_source =
    TPS_Par | TPS_Fun of Function_Common.info  | TPS_Def

    fun myprint_tac' ctxt  st = 
      let val _ = tracing ("..>");
          val _ = tracing (Thm.string_of_thm ctxt st)
      in all_tac st end

    fun myprint_tac ctxt str _ st = 
      let val _ = tracing ("..> " ^str);
          val _ = tracing (Thm.string_of_thm ctxt st)
      in all_tac st end



    fun dest_hol_flatten_eq_prop t =
      let
        val Const ("HOL.Trueprop", _) $ (Const ("HOL.eq", _) $ a $ b) = t
        val (Const ("Experiment.flatten", _) $ c) = a
      in (c, b) end
   fun split_off_typ (Type("fun",[S,T])) = 
              (case split_off_typ T of (L,Hd) => (S::L, Hd))
        | split_off_typ t = ([],t) 

      fun close_fun co ctxt = let   
        val co_ty = Term.type_of co
        val (es,e) = split_off_typ co_ty
        val nctxt = Variable.names_of ctxt    
        val vars = Name.invent nctxt "" (length es) 
        val vars = map Free (vars ~~ es)
        in
          (vars, fold (fn v => fn f => f $ v) vars co)
      end

      fun close_fun_schem co ctxt = let   
        val co_ty = Term.type_of co
        val (es,e) = split_off_typ co_ty
        val nctxt = Variable.names_of ctxt    
        val vars = Name.invent nctxt "" (length es) 
        val vars = map Var ((map (fn x => (x,0)) vars) ~~ es)
        in
          (vars, fold (fn v => fn f => f $ v) vars co)
      end

    fun add_partial_function bind def_eq =
      let
        val fixes = [(bind, NONE, NoSyn)];
        val specs = (fn def => ((Binding.empty, @{attributes [code]}), def)) def_eq
        val str = "heap"
      in
        Partial_Function.add_partial_function str fixes specs 
    end

    fun add_function bind defs =
      let
        val fixes = [(bind, NONE, NoSyn)];
        val specs = map (fn def => (((Binding.empty, []), def), [], [])) defs
        val pat_completeness_auto = fn ctxt =>
          Pat_Completeness.pat_completeness_tac ctxt 1
          THEN auto_tac ctxt
      in
        Function.add_function fixes specs Function_Fun.fun_config pat_completeness_auto
    end

    fun split_off_typ (Type("fun",[S,T])) = 
              (case split_off_typ T of (L,Hd) => (S::L, Hd))
        | split_off_typ t = ([],t)
    fun comb_typ (x::xs,Hd) = (Type("fun",[x,comb_typ (xs,Hd)])) 
        | comb_typ ([],Hd) = Hd
  

fun defined_by_partial_function ctxt t =
  (case t of Const (f_str, _) =>
      (length ( Proof_Context.get_thms ctxt (f_str^".raw_induct")) > 0)
               handle error => false
      | _ => false)

  fun getsource ctxt t = let
      val old_info = Function_Common.import_function_data t ctxt  
      val pf = defined_by_partial_function ctxt t
    in case old_info of SOME info => TPS_Fun info
          | NONE => (if pf then TPS_Par else TPS_Def )
      end

fun mono_side_tac ctxt = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} => ALLGOALS (
      SUBGOAL (fn (t, _) => case Logic.strip_imp_concl t of
        @{mpat "Trueprop (Heap_Time_Monad.mono_Heap ?a)"} => 
          Pf_Mono_Prover.mono_tac ctxt 1
       | 
        @{mpat "Trueprop (Heap_Monad.mono_Heap ?a)"} => 
          Pf_Mono_Prover.mono_tac ctxt 1
       |  _ => no_tac
      ))
    ) ctxt 

fun mkk binding def_thms termination ctxt =
  let 


    val fun_def = def_thms

    val eqns = map Thm.concl_of  def_thms
    val (eqns, _) = Variable.import_terms true eqns ctxt


    fun dest_hol_refines_prop' t = case t of
       Const ("Pure.all", _) $ t2 => dest_hol_refines_prop' t2
     | Abs (_,_,t) => dest_hol_refines_prop' t
     | Const ("HOL.Trueprop", _) $ t => dest_hol_refines_prop' t
     | (Const ("Transpile.refines", _) $ a $ b) => SOME (Term.head_of a,Term.head_of b)
     | _ => NONE

    fun dest_hol_refines_prop t =
      let
        val Const ("HOL.Trueprop", _) $ (Const ("Transpile.refines", _) $ a $ b) = t
      in (a, b) end
    fun dest_hol_eq_prop t =
      let
        val Const ("HOL.Trueprop", _) $ (Const ("HOL.eq", _) $ a $ b) = t
      in (a, b) end
    fun get_fun_term_head t =
      let
        val (t, _) = dest_hol_eq_prop t
        val t = Term.head_of t
     in t end
    fun get_fun_head t =
      let
        val (t, _) = dest_hol_flatten_eq_prop t
        val t = Term.head_of t
        val Const (fun_name, fun_ty) = t
     in (fun_name, fun_ty) end
   
  val _ = tracing "here"


    val src  = let
          val (lhs, rhs) = dest_hol_eq_prop (hd eqns)
          val (f, args) = Term.strip_comb lhs 
      in
          getsource ctxt f
      end

    val _ = (case src of TPS_Par => tracing ("defined via the partial function package!")
                | TPS_Fun _ => tracing "defined via the function package!"
                | TPS_Def => tracing "defined via the definition package!")

        fun convert t = 
          (case t of
             Type("fun",[S,T]) => let
                                     val S' = convert S
                                     val T' = convert T
                                  in Type("fun",[S',T']) end
            | Type("Heap_Time_Monad.Heap",xs) => Type("Heap_Monad.Heap",xs) 
            | _ => let val _ = tracing "rest" in t end
          )
        fun convert_term' f t  = 
          (case t of 
              t1 $ t2 => (convert_term' f t1) $ (convert_term' f t2)
            | (Free (f_n, f_ty)) => (if f then (Free (f_n, convert f_ty))
                                        else  (Var ((f_n,0), convert f_ty)) )
            | _ => t)
        val convert_term = convert_term' true

      (* for a defining equation synthesize a flattened equation theorem *)                            
      fun synthesize2 ctxt def_thm =
        let 
          val ctxt_orig = ctxt
          val fun_def = def_thm

          val eqn = Thm.concl_of def_thm

          val (lhs, rhs) = dest_hol_eq_prop eqn
          val (f, args) = Term.strip_comb lhs
 
          val t = @{mk_term "?lhs"} 
          val t_goal = @{mk_term "flatten ?lhs"} 
   
   
          val ([t,t_goal,eqn], ctxt) = (Variable.import_terms true) [t,t_goal,eqn] ctxt 
          val ty = Term.type_of t 
          val t_goaly = Term.type_of t_goal
          val  _ = tracing ("bra")

          val (th, tvars) = strip_comb t
          fun faa tc tt = let
              val _ = tracing "faa"  
              val (vc, p) = close_fun_schem tc ctxt   
              val pt = fold (fn v => fn f => f $ v) vc tt
              val (_, ctxt) = yield_singleton (Variable.import_terms true) p ctxt 
              val _ = tracing ("AA "  ^ (Syntax.string_of_term ctxt p))
              val refa = @{mk_term "Trueprop (refines ?p ?pt)"}
              fun purall t = @{mk_term "Pure.all ?t"}
              val tea = fold_rev (purall oo lambda) (  vc   ) refa 
            val _ = tracing ("YE"^ Syntax.string_of_term ctxt tea) 
            val _ = tracing ("YE"^ Syntax.string_of_term ctxt tea) 
           
              in  tea
              end

          fun fa t = let val t_c = convert_term' false t
                  val t_c_ty = Term.type_of t_c
                  val t_ty = Term.type_of t
                  val b = (t_c_ty = t_ty) in (if b then [] else [faa t_c t]) end


        val _ = tracing "====Y"
          val tvars = (map fa tvars)
          val ff =  fold (fn x => fn y => x @ y) tvars []
          val _ = map (fn t => tracing (Syntax.string_of_term ctxt t)) ff

          val (ff, ctxt) = (Variable.import_terms true) ff ctxt 

          val v = Var (("result",0), t_goaly)

          val goalhead = @{mk_term "Trueprop (refines ?v ?t)"}
          val g = fold (fn t => fn g => @{mk_term "Pure.imp ?t ?g"}) ff goalhead
          val  _ = tracing ("goalAA " ^ Syntax.string_of_term ctxt g)
    
   

          val  _ = tracing ("ff")
          val  _ = tracing ("t " ^ Syntax.string_of_term ctxt t)
          val  _ = tracing ("ty " ^ Syntax.string_of_typ ctxt ty)
          val goal = g |> Thm.cterm_of ctxt
          val  _ = tracing ("goal " ^ Syntax.string_of_term ctxt @{mk_term "Trueprop (refines ?v ?t)"})
    

          val  _ = tracing ("fnn")
          val transpile_rules =  (Named_Theorems_Rev.get ctxt @{named_theorems_rev transpile_rules})



          val flatten_rules =  ( transpile_rules   ) |> Tactic.build_net
          val last_resort =  (   [@{thm refines_flatten}] ) |> Tactic.build_net
          val _ = EqSubst.eqsubst_tac
          fun tac ctxt =  (ALLGOALS ((EqSubst.eqsubst_tac ctxt [0] [fun_def]  )
                  THEN' (TRY_SOLVED' (REPEAT_DETERM' (CHANGED o 
                      FIRST' [ resolve_from_net_tac ctxt flatten_rules,
                                Method.assm_tac ctxt,
                               resolve_from_net_tac ctxt last_resort, 
                                mono_side_tac ctxt ])))))

          (* synthesize by using flatten rules *)
          val thm = Goal.prove_internal ctxt [] goal (fn _ => tac ctxt)

          val  _ = tracing ("proof successfull")
        
        in
          singleton (Variable.export ctxt ctxt_orig) thm
        end  

    val flat_thms = map (synthesize2 ctxt) def_thms
    val _ = map (fn thm => tracing (Thm.string_of_thm ctxt thm)) flat_thms
  
  val _ = tracing "here2"
    (* give the theorem a name *)
    val (_, ctxt) = Local_Theory.note (
      (Binding.qualify_name true binding "flattens", []),
      flat_thms
    ) ctxt  

    val thm = hd flat_thms

    val s = Binding.name_of binding
      
    
    fun prepare_equation ctxt (def_thm, flat_thm) =
      let 
        val ctxt_orig = ctxt
        val  _ = tracing ("prepare_equation")
        val (f_name, f_ty, args) = let
            val eqn = Thm.concl_of def_thm
            val (eqn , ctxt1) = yield_singleton (Variable.import_terms true) (eqn ) ctxt
            val (lhs, rhs) = dest_hol_eq_prop eqn
            val (f, args) = Term.strip_comb lhs
            val Const (f_name, f_ty) = f
          in 
            (f_name, f_ty, args)
          end
        val orig_head = Const (f_name, f_ty)
      

        val _ = tracing "convert"
        val _ =        tracing (Syntax.string_of_typ ctxt f_ty)
        val f_ty' =        convert f_ty
        val _ =        tracing (Syntax.string_of_typ ctxt f_ty')

        

        val fl_eqn = Thm.concl_of flat_thm
        val prems = Thm.prems_of flat_thm
        val  _ = tracing ("before " ^ Syntax.string_of_term ctxt fl_eqn)
        val (fl_eqn::prems, ctxt1) = (Variable.import_terms true) (fl_eqn::prems) ctxt


        val _ = map (fn prem => tracing (Syntax.string_of_term ctxt prem)) prems
        val substs = map (dest_hol_refines_prop') prems
        val _ = map (fn prem => case prem of NONE => tracing "NONE"
                |  SOME (a,b) =>  tracing (Syntax.string_of_term ctxt a)) substs
        fun sw (x,y) = (y,x)
        val substs = map (sw o the) substs    
        val _ = tracing ("len: " ^ ( Int.toString (length substs)))
        val _ = map (fn (x,y) => tracing (Syntax.string_of_term ctxt x ^","^Syntax.string_of_term ctxt y)) substs

        val _ = (case src of TPS_Def => ()
                   | _ => if (length substs > 0)
                            then error "Recursive higher-order functions are not supported!"
                            else ())
        

        val _ = tracing ("after " ^ Syntax.string_of_term ctxt1 fl_eqn)
        val _ = Specification.read_multi_specs
        fun my_replace t v = let
          val  _ = tracing "start my_replace"
          fun r (t1$t2) =  
              let
                val found = (case t1 of (Const ("Transpile.flatten", _))
                  => let
                      val hot2 = Term.head_of t2 
                      val _ = tracing (Syntax.string_of_term ctxt1 hot2)
                     in (case hot2 of (Const (f_name, _)) =>
                                (* replace *)
                             let val (f,fs) = strip_comb t2
                                     in 
                              (if f <> orig_head then error ("Missing flatten rule for " ^ Syntax.string_of_term ctxt f) else
                           SOME (list_comb (v, map (Term.subst_free substs) fs))   ) end
                            | (Free (f_name, f_ty)) => let
                                  val (f,fs) = strip_comb t2 in SOME (list_comb ( Term.subst_free substs hot2 ,
                                                        map (Term.subst_free substs) fs)) end
                           | _ => NONE)
                     end
                  | _ =>   NONE)
                in (case found of SOME t' => t'
                     | NONE => r t1  $ r t2 )
              end
            | r (Abs (x,T,t))  =
                let val t = r t 
                in (Abs (x,T,t)) end
            | r t = t
          in r t
          end 

        val  _ = tracing ("split " ^ Syntax.string_of_term ctxt fl_eqn)
        val (rhs,lhs) = dest_hol_refines_prop fl_eqn
        val lhs = @{mk_term "flatten ?lhs"}
        val (es,e) = split_off_typ f_ty
        val ee = comb_typ (es, Term.type_of lhs)
        val ee = convert ee
        val vv =   Free (s, ee) 

        val R = my_replace lhs vv  
        val _ = tracing (Syntax.string_of_term ctxt R)
        val RR = my_replace rhs vv   
        
        val _ = tracing (Syntax.string_of_term ctxt RR)
        val feq = @{mk_term "Trueprop (?R = ?RR)"} 
     (*   val feq = singleton  (Variable.export_terms ctxt1 ctxt_orig) feq *)
      in  feq end
 

    val feq2 = map (prepare_equation ctxt) (def_thms ~~ flat_thms)
 
    val _ = tracing "defining equations:"
    val _ = map (fn x => tracing (Syntax.string_of_term ctxt x)) feq2
    val _ = tracing "aha"
 



    val ctxt = (case src of
               TPS_Par =>
                let
                  val _ =  tracing ("defined via the partial function package!")
                  val [feq2] = feq2
                  val ((t, _), ctxt) = add_partial_function binding feq2 ctxt
                in ctxt end
              | TPS_Def => 
                  let
                  val [feq2] = feq2
                    val _ = tracing "normal definition, not recursive!" 
                    
                    val ((_,(_,def_thm)),ctxt) =
                           Specification.definition 
                                    (SOME (binding,NONE,Mixfix.NoSyn)) [] []
                                     ((Binding.empty,@{attributes [code]}),feq2) ctxt
                    in ctxt end 
              | TPS_Fun _ =>
            let
              val _ =  tracing "defined via the function package!"
              val (new_info, ctxt) = add_function binding feq2 ctxt
            in ctxt  end )
 

   val _ = tracing "oha"
  in
    (ctxt )
  end

fun transpile_define_cmd ((termination, binding), thm_refs) lthy =
  let
    val def_thms = Attrib.eval_thms lthy thm_refs
  val _ = tracing "transpile_define"
  val  ctxt  = mkk binding def_thms (termination <> NONE) lthy
  in
      ctxt
  end

val transpile_define_parser =
  Scan.option (Parse.$$$ "(" |-- Parse.reserved "prove_termination" --| Parse.$$$ ")")
  -- (Parse.binding --| Parse.$$$ ":") (* scope, e.g., bf\<^sub>T *)
  -- Parse.thms1

val _ =
  Outer_Syntax.local_theory @{command_keyword transpile_define}
  "Transpile from Imperative-HOL with time to vanilla Imperative-HOL, stripping away time counting"
    (transpile_define_parser >> transpile_define_cmd)


fun transpile_replay_cmd  (t_new, t_old) ctxt =
  let
    val t_new = Syntax.read_term ctxt t_new;
    val SOME new_info = Function_Common.import_function_data t_new ctxt
    val t_old = Syntax.read_term ctxt t_old;
    val old_info = Function_Common.import_function_data t_old ctxt
    
  fun totality_replay_tac old_info new_info ctxt =
    let
      val totality0 = Transform_Misc.totality_of old_info
      val def0 = Transform_Misc.rel_of old_info ctxt
    val _ = tracing ("AA") 
  val _ = tracing (Thm.string_of_thm ctxt def0) 
      val def1 = Transform_Misc.rel_of new_info ctxt
  val _ = tracing (Thm.string_of_thm ctxt def1) 
      fun my_print_tac msg st = (tracing msg; all_tac st)
    in  (Transform_Tactic.totality_resolve_tac totality0 def0 def1 ctxt
        THEN my_print_tac "termination by replaying") 
    end
 
    val lthy = ctxt

    val replay_tac = case old_info of
      NONE => no_tac
    | SOME info => 
      myprint_tac' ctxt THEN totality_replay_tac info new_info lthy
    val totality_tac =
      myprint_tac' ctxt THEN
      ((
      myprint_tac' ctxt THEN replay_tac)
      ORELSE (Function_Common.termination_prover_tac false lthy
        THEN Transform_Tactic.my_print_tac "termination by default prover"))

    val (_, ctxt) = Function.prove_termination NONE replay_tac lthy
 
    val _ = tracing "fff_cmd"
  in
    ctxt
end

val transpile_replay_parser =
   Parse.term  --
   Parse.term 
 
val _ =
  Outer_Syntax.local_theory @{command_keyword transpile_replay}
  "Define a new ground constant from an existing function definition"
    (transpile_replay_parser >> transpile_replay_cmd)
\<close>



subsection \<open>transpile_prove\<close>

lemma ff1: "a=a' \<Longrightarrow> b=b' \<Longrightarrow> Heap_Monad.bind a b =  Heap_Monad.bind a' b'"
  by auto
lemma ff: "a=a' \<Longrightarrow> (\<And>x. b x = b' x) \<Longrightarrow> Heap_Monad.bind a b =  Heap_Monad.bind a' b'"
  apply(rule ff1) apply simp apply (rule ext) by simp

lemma rr: "\<And>aa. (aa \<Longrightarrow> b=b') \<Longrightarrow> (~aa\<Longrightarrow> c=c') \<Longrightarrow> (if aa then b else c) = (if aa then b' else c')"
  apply auto done


ML\<open>

fun mkk2 t t2 ctxt =
  let 
    val transpile_rules =  (Named_Theorems_Rev.get ctxt @{named_theorems_rev transpile_rules})

    fun split_off_typ (Type("fun",[S,T])) = 
              (case split_off_typ T of (L,Hd) => (S::L, Hd))
        | split_off_typ t = ([],t)
    val _ = tracing "mkk2"    
  
    val te = Syntax.read_term ctxt t;
    val (varsb,psc) = close_fun_schem te ctxt  

    val te2 = Syntax.read_term ctxt t2;
    val (varsb,ppsc) = close_fun_schem te2 ctxt 

    val goal_t = @{mk_term "Trueprop (refines ?psc ?ppsc)"} 

    val old_info  = Function_Common.import_function_data te ctxt   

    val _ = (case old_info of NONE => tracing (Syntax.string_of_term ctxt te
                                           ^ " was defined via the partial function package")
            | SOME old_info => tracing (Syntax.string_of_term ctxt te
                                           ^ " was defined via the function package"))  

    fun via_part_fun te te2 varsb = let
      fun mk_effect ctxt psc =
        let  
          val ef = @{mk_term "effect ?psc"}
          val (_, ctxt) = yield_singleton (Variable.import_terms true) ef ctxt
          val (vc, p) = close_fun_schem ef ctxt   
          val (_, ctxt) = yield_singleton (Variable.import_terms true) p ctxt
          
          val nctxt = Variable.names_of ctxt    
          val vars = Name.invent nctxt "" 1 
          val vars_n = map Var ((map (fn x => (x,0)) vars) ~~ [natT])
          
          val _ = tracing ("AA "  ^ (Syntax.string_of_term ctxt p))
          val tea = fold_rev lambda (varsb @ vc @ vars_n ) p
          val _ = tracing ("C "  ^ (Syntax.string_of_term ctxt tea))
        in tea end

      val insta = mk_effect ctxt psc
      val _ = tracing ("INSTA"  ^ (Syntax.string_of_term ctxt insta))
  
      
  
      (* try to prove the goal *)
      fun prove_goal ctxt goal =
        let
          val ctxt_orig = ctxt
          val (goal :: varsb, ctxt) =  Variable.import_terms true (goal :: varsb) ctxt
          val _ = tracing (Syntax.string_of_term ctxt goal)
          val Const ("HOL.Trueprop", _) $ goal_t_bool = goal 
          val goal_t = goal 
          val _ = tracing ("GoAL:"^Syntax.string_of_term ctxt goal_t)
          val goal = goal |> Thm.cterm_of ctxt  
  
          val my_ss = put_simpset HOL_basic_ss ctxt addsimps @{thms   Let_def}
            (* delsimps @{thms binarysearch.simps blas.simps} *)
          val f = Context_Rules.add Classical.safe_intro Classical.unsafe_intro Context_Rules.intro_query
  
        
          fun string_of_thms ctxt args =
            Pretty.string_of (Proof_Context.pretty_fact ctxt ("", Attrib.eval_thms ctxt args));
   
  
          val Const ("Transpile.refines", _) $ L $ R  = goal_t_bool 
  
          val Const (te2_str, _) = te2 
          
          val _ = tracing "wee"
          val ee = hd ( Proof_Context.get_thms ctxt (te2_str^".raw_induct"))

          val Const (te_str, _) = te 
          val f'_simps = ( Proof_Context.get_thms ctxt (te_str^".simps"))

          val _ = tracing (Thm.string_of_thm ctxt ee)
          
          val ee_vars = rev (Term.add_vars (Thm.full_prop_of ee) [])
          val _ = map (fn (_,ty) => tracing (Syntax.string_of_typ ctxt ty)) ee_vars
          
          val ggg = (if length ee_vars = 6 
            then
              let 
                val _ = tracing "TUPLED"
                val ff = foldl1 HOLogic.mk_prod varsb 
          
                val _ = tracing (Syntax.string_of_term ctxt ff)
          
                val gg = infer_instantiate' ctxt  [NONE,SOME (Thm.cterm_of ctxt ff)] ee 
                val _ = tracing (Thm.string_of_thm ctxt gg)
                val ggg = asm_full_simplify 
    (put_simpset HOL_ss ctxt 
      addsimps @{thms prod.case}) gg
                val _ = tracing (Thm.string_of_thm ctxt ggg)
              in ggg end
            else 
              let
                val _ = tracing "not TUPLED"
                val insts = map (SOME o Thm.cterm_of ctxt) varsb
                val gg = infer_instantiate' ctxt  (NONE :: insts) ee 
              in
                 gg
              end)
            val gggg = infer_instantiate' ctxt  [SOME (Thm.cterm_of ctxt insta)] ggg 
   
            val _ = tracing ("yip" ^ Thm.string_of_thm ctxt gggg)
  
  
            fun tac ctxt =  (HEADGOAL (myprint_tac ctxt "AA"
          THEN' resolve_tac ctxt @{thms refinesI}
  THEN' myprint_tac ctxt "AB" THEN' simp_tac ctxt
  THEN' myprint_tac ctxt "AC"
          THEN' resolve_tac ctxt [gggg]
  THEN' myprint_tac ctxt "AD" )) THEN print_tac ctxt "all" THEN
            asm_full_simp_tac ctxt 2
          THEN eresolve_tac ctxt (@{thms refinesD1[OF _ , rotated]} @ [asm_rl]) 1
          THEN (HEADGOAL ( EqSubst.eqsubst_tac ctxt [0] f'_simps
                THEN' myprint_tac ctxt "aaae"
                 THEN'  REPEAT_DETERM' ( FIRST' [ resolve_tac ctxt transpile_rules,
                 resolve_tac ctxt @{thms refinesI} THEN' Method.assm_tac ctxt]
                       THEN' myprint_tac ctxt "ae" )))
  
          val thm = Goal.prove_internal ctxt [] goal (fn _ => tac ctxt) 
   
          val thm = singleton (Variable.export ctxt ctxt_orig) thm
   
          val  Const (fun_name, fun_ty) = te
          val defname = Binding.name fun_name
  
          val _ = tracing ("UNDER"^Syntax.string_of_term ctxt te)
          val (_, ctxt) = Local_Theory.note (
            (Binding.qualify_name true defname "correct_translate", @{attributes [transpile_rules]}),
            [thm]
          ) ctxt_orig 
        in
          ctxt
        end
  
       val ctxt = prove_goal ctxt goal_t  
      in  
        ctxt
      end

    fun via_fun u = let 
        val goal = goal_t 
        val ctxt_orig = ctxt
        val (goal, ctxt) = yield_singleton (Variable.import_terms true) goal ctxt
        val _ = tracing (Syntax.string_of_term ctxt goal)
        val Const ("HOL.Trueprop", _) $ goal_t_bool = goal 
        val goal_t = goal 
        val _ = tracing ("GoAL:"^Syntax.string_of_term ctxt goal_t)
        val goal = goal |> Thm.cterm_of ctxt  
        val rules = transpile_rules |> Tactic.build_net
   
  
        val aee = (case Function_Common.import_function_data te2 ctxt of
                  SOME info => info
                | NONE => error ("Not a function: " ^ quote (Syntax.string_of_term ctxt te2)))
        
      
        val { termination, fs, R, add_simps, case_names, psimps,
          pinducts, defname, fnames, cases, dom, pelims, simps, inducts,  ...} = aee
    
        val simp = (case simps of NONE => error ("Simp rule not available!")
                  | SOME simps => simps)
        val inducts = (case inducts of NONE => error ("Simp rule not available!")
                  | SOME inducts => inducts)
     
     
  
        val Const (te2_str, _) = te2  
        val f_simps = ( Proof_Context.get_thms ctxt (te2_str^".simps"))
    
        val induction_rule = Function.get_info ctxt te2 |> #inducts |> the
        val f'_simps = Function.get_info ctxt te |> #simps |> the
                         

        fun mk_effect ctxt =
          let  
            val ef = @{mk_term "refines ?psc ?ppsc"}
            val (_, ctxt) = yield_singleton (Variable.import_terms true) ef ctxt
            
            val nctxt = Variable.names_of ctxt    
            val vars = Name.invent nctxt "" 1 
            val vars_n = map Var ((map (fn x => (x,0)) vars) ~~ [natT])
            
            val _ = tracing ("AA "  ^ (Syntax.string_of_term ctxt ef))
            val tea = fold_rev lambda (varsb  ) ef
            val _ = tracing ("C "  ^ (Syntax.string_of_term ctxt tea))
          in tea end

        val _ = tracing (Thm.string_of_thm ctxt (hd induction_rule))
        val insta = mk_effect ctxt
        val insta_ir =  infer_instantiate' ctxt  [SOME (Thm.cterm_of ctxt insta)] (hd induction_rule) 
   
        val _ = tracing ("yip" ^ Thm.string_of_thm ctxt insta_ir)
        val _ = tracing "f_simps"
        val _ = map (fn thm => tracing (Thm.string_of_thm ctxt thm)) f'_simps
        
        val _ = tracing ("WHAT")
    
        fun tac ctxt =  (ALLGOALS (myprint_tac ctxt ""
          THEN' resolve_tac ctxt [insta_ir]
          THEN_ALL_NEW ( myprint_tac ctxt "there1"  (* why is this executed twice ? *)
            THEN' (EqSubst.eqsubst_tac ctxt [0] f_simps  )
            THEN' myprint_tac ctxt "there2"
            THEN' (EqSubst.eqsubst_tac ctxt [0] f'_simps 
            THEN' myprint_tac ctxt "there3"
            THEN' REPEAT_DETERM' (CHANGED o (
                     FIRST' [resolve_tac ctxt transpile_rules,
                              Method.assm_tac ctxt  ] )
          ))))) 
    
        val thm = Goal.prove_internal ctxt [] goal (fn _ => tac ctxt) 
     
        val thm = singleton (Variable.export ctxt ctxt_orig) thm
    
        val defname =  Function_Common.import_function_data te ctxt
              |> the |> #defname
    
        val _ = tracing ("UNDER"^Syntax.string_of_term ctxt te)
        val (_, ctxt) = Local_Theory.note (
          (Binding.qualify_name true defname "correct_translate", @{attributes [transpile_rules]}),
          [thm]
        ) ctxt_orig   
      in
        ctxt
      end


    fun via_def u = let
        val _ = ()
        val Const (te_str, _) = te  
        val f'_flattens = ( Proof_Context.get_thms ctxt (te_str^".flattens"))
        val [f'_def] = ( Proof_Context.get_thms ctxt (te_str^"_def")) 
        val _ =  tracing (Thm.string_of_thm ctxt f'_def) 
        val folded_r_thms = map (Local_Defs.fold ctxt [f'_def]) f'_flattens
        val _ = map (fn th => tracing (Thm.string_of_thm ctxt th)) folded_r_thms
        val Const (fun_name, fun_ty) = te
        val defname = Binding.name fun_name
        val (_, ctxt) = Local_Theory.note (
          (Binding.qualify_name true defname "correct_translate", @{attributes [transpile_rules]}),
          folded_r_thms
        ) ctxt  
      in
        ctxt
      end


    val ctxt = (case old_info of NONE => 
          (if defined_by_partial_function ctxt te then via_part_fun te te2 varsb
            else via_def ())
        | SOME old_info => via_fun ())  

    
  in ctxt
end


fun transpile_prove_cmd (binding1, binding2) lthy =
  let 
    val _ = tracing "transpile_prove"
    val ctxt =  mkk2 binding1 binding2 lthy 
  in
    ctxt
  end

val transpile_prove_parser = Parse.term -- Parse.term 

val _ =
  Outer_Syntax.local_theory @{command_keyword transpile_prove}
  "Define a new ground constant from an existing function definition"
    (transpile_prove_parser >> transpile_prove_cmd)

\<close>


subsection \<open>Setup \<close>



  lemma HTM_heap_fixp_codegen:
    assumes DEF: "f \<equiv> Heap_Monad.heap.fixp_fun cB"
    assumes M: "(\<And>x. Heap_Monad.mono_Heap (\<lambda>f. cB f x))"
    shows "f x = cB f x"
    unfolding DEF
    apply (rule fun_cong[of _ _ x])
    apply (rule Heap_Monad.heap.mono_body_fixp)
    apply fact
    done


  ML \<open>
    structure Sepref_Extraction = struct
      val heap_extraction: Refine_Automation.extraction = {
          pattern = Logic.varify_global @{term "Heap_Monad.heap.fixp_fun x"},
          gen_thm = @{thm HTM_heap_fixp_codegen},
          gen_tac = (fn ctxt => 
            Pf_Mono_Prover.mono_tac ctxt
          )
        }

      val setup = I 
        (*#> Refine_Automation.add_extraction "trivial" triv_extraction*)
        #> Refine_Automation.add_extraction "heap" heap_extraction

    end
    \<close>

setup Sepref_Extraction.setup 



end