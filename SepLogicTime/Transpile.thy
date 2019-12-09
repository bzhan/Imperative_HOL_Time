theory Transpile
imports "SepAuto_Time" BinarySearch_Impl DynamicArray2
    "Separation_Logic_Imperative_HOL.Hoare_Triple"  
  "Refine_Imperative_HOL.Term_Synth" "Monad_Memo_DP.Transform_Cmd"
  "Refine_Imperative_HOL.Pf_Mono_Prover"
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

lemma Array_length_conv: "Array_Time.length h a = Array.length h a"
  unfolding Array_Time.length_def Array.length_def Array_get_conv by simp

subsection \<open>forget\<close>


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

lemma forget_it: 
  "forget ($n) = emp"
    "forget (A * B) = forget A * forget B"
  "forget true = true"
  "forget false = false"
  "forget (p \<mapsto>\<^sub>a xs) = p \<mapsto>\<^sub>a xs"
  "forget (q \<mapsto>\<^sub>r v) = q \<mapsto>\<^sub>r v"
  "forget (\<up>P) = \<up>P"
  subgoal unfolding timeCredit_assn_def
    unfolding one_assn_def 
     apply(subst   SepAuto_Time.Abs_assn_inverse   )
    subgoal apply auto
      unfolding SepAuto_Time.proper_def by auto 
    apply(rule arg_cong[where f=Assertions.assn.Abs_assn])
    apply(rule ext) by auto 
  subgoal 
    apply (rule  ) apply rule
    subgoal for h unfolding mod_star_conv
      apply auto unfolding assn_fn_models_conv
      apply(drule SepAuto_Time.mod_star_convE) apply auto
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
      apply auto
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
      sorry


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




subsubsection \<open>refines for combinators\<close>

lemma refines_combinators: 
  "refines m' m \<Longrightarrow> (\<And>v. refines (f' v) (f v)) \<Longrightarrow> refines (m' \<bind> f') (m \<bind> f)"
    "refines x' x \<Longrightarrow> refines y' y \<Longrightarrow> refines (if b then x' else y') (if b then x else y)"
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

subsubsection \<open>Refines for basic operations\<close>

lemma refines_nth:
    "refines (Array.nth a l) (Array_Time.nth a l)"
  unfolding refines_def Heap_Time_Monad.effect_def Heap_Monad.effect_def
          Array_Time.nth_def  Array.nth_def 
          Heap_Time_Monad.guard_def  Heap_Monad.guard_def
    by (auto simp: Array_length_conv Array_get_conv)


named_theorems_rev transpile_rules
      "Rules for transpiling from Imperative-HOL with time
        to vanilla Imperative-HOL"


lemmas [transpile_rules] = refines_combinators refines_nth

section \<open>Transpilation by hand -- an example\<close>

schematic_goal p: "refines ?G (binarysearch l r x a)"   
  apply(subst binarysearch.simps)
  apply(rule transpile_rules refines_flatten)+ done

partial_function (heap) aahh where
"aahh l r x a = (if r \<le> l then Heap_Monad.return False
  else if r \<le> l + 1 then Array.nth a l \<bind> (\<lambda>v. Heap_Monad.return (v = x))
       else let b = avg l r
            in Array.nth a b \<bind>
               (\<lambda>c. if c = x then Heap_Monad.return True
                    else if c < x then aahh (b + 1) r x a else aahh l b x a))"

lemma refines_binarysearch: "refines (aahh l r x a) (binarysearch l r x a)"
  unfolding refines_def
proof safe
  fix h h' ra n
  assume *: "Heap_Time_Monad.effect (binarysearch l r x a) h h' ra n"
  
  note f =  binarysearch.raw_induct[where P="\<lambda>l r x a h h' ra n. Heap_Monad.effect (aahh l r x a) h h' ra", where xa="(((l,r),x),a)", simplified]

  show "Heap_Monad.effect (aahh l r x a) h h' ra" 
  proof (rule f[OF _ *], goal_cases) 
    case (1 f l r x a la ra xa aa)
    from 1(1) have IH: "\<And>l r x a. refines (aahh l r x a) (f l r x a) " unfolding refines_def by auto 
    show ?case apply(rule refinesD1[OF _ 1(2)])
      apply(subst aahh.simps)
      apply(rule transpile_rules IH)+
      done
  qed
qed

thm refines_HT'[OF _ refines_binarysearch]


lemma flatten_correct: "sorted xs \<Longrightarrow> r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs > aahh l r x a
       <\<lambda>ra. a \<mapsto>\<^sub>a xs * \<up> (ra = (\<exists>i\<ge>l. i < r \<and> xs ! i = x))>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule refines_binarysearch)
    apply(rule binarysearch_correct')
      apply simp
     apply simp
    apply simp
   apply (simp add: forget_it)
  apply(rule ext) apply (simp add: forget_it)
  done 




end