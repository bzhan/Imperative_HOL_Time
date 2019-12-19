theory Transpile_Tests
  imports
  "SeprefTime.EdmondsKarp_Time"
  Transpile BinarySearch_Impl
 RBTree_Impl Skew_Heap_Impl DynamicArray2
      "SeprefTime.Remdups" "SeprefTime.Kruskal_Time"
  
 "SeprefTime.FW_Code"
  MergeSort_Impl

   "HOL-Library.Code_Target_Numeral"
begin

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



subsection  \<open>Higher Order functions\<close>


partial_function (heap) imp_for'' :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for'' i u f s = (if i \<ge> u then return s else f i s \<bind> imp_for'' (i + 1) u f)"

lemma 
    refines_imp_for[transpile_rules]: 
  assumes "(\<And>x y. refines (f' x y) (f x y))"
  shows "refines (imp_for'' i u f' s) (imp_for' i u f s)"
  unfolding refines_def
proof safe
  fix h h' ra n
  assume *: "Heap_Time_Monad.effect (imp_for' i u f s) h h' ra n"
  
  note f =  imp_for'.raw_induct[where P="\<lambda>i u ff s h h' ra n. ff=f \<longrightarrow>  Heap_Monad.effect (imp_for'' i u f' s) h h' ra"]

  have  "f = f \<longrightarrow> Heap_Monad.effect (imp_for'' i u f' s) h h' ra" 
  proof (rule f[OF _ *], goal_cases) 
    case (1 rec i u ff a la ra xa aa)
    from 1(1) have IH: "\<And>i u ff s. ff=f \<Longrightarrow> refines (imp_for'' i u f' s) (rec i u ff s) " unfolding refines_def by auto 
    show ?case apply safe apply(rule refinesD1[OF _ 1(2)])
      apply(subst imp_for''.simps)
      apply (simp only:) (* propagate the ff=f *)
      apply(rule transpile_rules IH assms | simp)+ 
      done
  qed
  then show " Heap_Monad.effect (imp_for'' i u f' s) h h' ra" by simp
qed
 

definition comb :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow>  'a Heap_Time_Monad.Heap) \<Rightarrow> (nat \<Rightarrow>  'b Heap_Time_Monad.Heap) \<Rightarrow> ('a*'b) Heap_Time_Monad.Heap"
    where "comb n f g = do { fx \<leftarrow> f n n; gx \<leftarrow> g n; Heap_Time_Monad.return (fx,gx) } "
term Pure.imp
term "refines v t"
transpile_define comb': comb_def
print_theorems
transpile_prove comb' comb
print_theorems
 
transpile_define imp_for'2: imp_for'.simps 
 
section "Example -- MergeSort"


thm mergeSort_correct
 
transpile_define atake': atake_def
transpile_prove atake' atake


transpile_define adrop': adrop_def
transpile_prove adrop' adrop

transpile_define mergeinto': mergeinto.simps
transpile_replay mergeinto' mergeinto
transpile_prove mergeinto' mergeinto

transpile_define merge_sort_impl': merge_sort_impl.simps
transpile_prove merge_sort_impl' merge_sort_impl
print_theorems

thm prod.case

lemma merge_sort_impl'_correct:
  "<p \<mapsto>\<^sub>a xs> merge_sort_impl' p <\<lambda>_. p \<mapsto>\<^sub>a sort xs>\<^sub>t" 
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.merge_sort_impl'.correct_translate)
    apply(rule mergeSort_correct) 
   apply (simp add: forget_it) 
  apply (simp add: forget_it)
  done


section \<open>Example -- Dynamic Array\<close>

lemma [transpile_rules]: "(\<And>al ar. refines (f' al ar) (f al ar)) \<Longrightarrow>
    refines (case x  of  Dyn_Array al ar \<Rightarrow> f' al ar) (case x  of  Dyn_Array al ar \<Rightarrow> f al ar)" 
  by(auto split: dynamic_array.splits)



transpile_define array_copy': array_copy.simps
transpile_replay array_copy' array_copy
transpile_prove array_copy' array_copy 

transpile_define push_array': push_array_def[unfolded array_max_def array_length_def
                                              push_array_basic_def double_length_def]
transpile_prove push_array' push_array

transpile_define dfilter_aux': dfilter_aux.simps
transpile_replay dfilter_aux' dfilter_aux
transpile_prove dfilter_aux' dfilter_aux


text \<open>an alternative way to synthesize\<close>
experiment
begin
schematic_goal refines_dyn_array_new:  "refines ?G dyn_array_new"
  unfolding dyn_array_new_def 
  apply(rule transpile_rules )+ 
    done
concrete_definition dyn_array_new'  uses refines_dyn_array_new is "refines ?G dyn_array_new"
print_theorems
lemmas [transpile_rules] = dyn_array_new'.refine
end

transpile_define dyn_array_new': dyn_array_new_def
transpile_prove dyn_array_new' dyn_array_new

transpile_define dfilter_impl': dfilter_impl_def
transpile_prove dfilter_impl' dfilter_impl
print_theorems

lemma "<a \<mapsto>\<^sub>a xs> dfilter_impl' a P
       <\<lambda>r. a \<mapsto>\<^sub>a xs * forget (dyn_array (filter P xs) r)>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.dfilter_impl'.correct_translate)
    apply(rule dfilter_impl_rule) 
   apply (simp add: forget_it) 
  apply (simp add: forget_it)
  done

export_code dfilter_impl' in SML


transpile_define destroy': destroy_def
transpile_prove destroy' destroy


subsection \<open>Example -- binarysearch\<close>

transpile_define   binarysearch': binarysearch.simps
transpile_prove binarysearch' binarysearch

lemma binarysearch'_HT: "sorted xs \<Longrightarrow> r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs > binarysearch' l r x a
       <\<lambda>ra. a \<mapsto>\<^sub>a xs * \<up> (ra = (\<exists>i\<ge>l. i < r \<and> xs ! i = x))>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.binarysearch'.correct_translate)
    apply(rule binarysearch_correct')
      apply (simp_all  add: forget_it) 
  done


section "Example -- Red Black Tree"

fun rbt_btree :: "('a::heap, 'b::heap) rbt \<Rightarrow> ('a, 'b) rbt_node ref option \<Rightarrow> Assertions.assn" where
  "rbt_btree RBTree.Leaf p = \<up>(p = None)"
| "rbt_btree (rbt.Node lt c k v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r RBTree_Impl.Node lp c k v rp * rbt_btree lt lp * rbt_btree rt rp)"
| "rbt_btree (rbt.Node lt c k v rt) None = false"

lemma forget_rbt_btree[forget_it]: "forget (RBTree_Impl.btree t p) = rbt_btree t p"
  apply(induction t arbitrary: p) apply (auto simp: forget_it)
  subgoal for t1 x2 x3 x4 t2 p apply (cases p) apply (auto simp: forget_it)
    done
  done

schematic_goal forget_rbt_map_assn: "forget (rbt_map_assn M b) = ?G"
  unfolding rbt_map_assn_def
  apply(subst forget_it)+
  by(rule refl)
concrete_definition rbt_map_assn_flat uses forget_rbt_map_assn
lemmas [forget_it] = rbt_map_assn_flat.refine
thm rbt_map_assn_flat_def

transpile_define get_color': get_color_def
transpile_prove get_color' get_color

transpile_define set_color': set_color_def
transpile_prove set_color' set_color

transpile_define btree_rotate_r': btree_rotate_r_def
transpile_prove btree_rotate_r' btree_rotate_r

transpile_define btree_rotate_l': btree_rotate_l_def
transpile_prove btree_rotate_l' btree_rotate_l 

transpile_define btree_balanceR': btree_balanceR_def
transpile_prove btree_balanceR' btree_balanceR 

transpile_define btree_balance': btree_balance_def
transpile_prove btree_balance' btree_balance
 

transpile_define btree_constr': btree_constr_def
transpile_prove btree_constr' btree_constr 

transpile_define rbt_ins': rbt_ins.simps
transpile_prove rbt_ins' rbt_ins

transpile_define rbt_paint': RBTree_Impl.paint_def
transpile_prove rbt_paint' RBTree_Impl.paint

transpile_define rbt_insert': rbt_insert_def
transpile_prove rbt_insert' rbt_insert 

lemma rbt_insert'_HT:  "<rbt_map_assn_flat M b> 
      rbt_insert' k v b
     <rbt_map_assn_flat (M {k \<rightarrow> v})>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.rbt_insert'.correct_translate)
    apply(rule rbt_insert_rule)
      apply (simp add: forget_it)
      apply (simp add: forget_it) 
  done

transpile_define rbt_search': rbt_search.simps
transpile_prove rbt_search' rbt_search

lemma rbt_search'_HT:  "<rbt_map_assn_flat M b> 
     rbt_search' x b
     <\<lambda>r. rbt_map_assn_flat M b * pure_assn(r = M\<langle>x\<rangle>)>\<^sub>t"
  (* oddity: using \<up> syntax does lead to exceptoion:
     exception COERCION_GEN_ERROR fn raised (line 678 of "~~/src/Tools/subtyping.ML") *)
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.rbt_search'.correct_translate)
    apply(rule rbt_search)
      apply (simp add: forget_it)
      apply (simp add: forget_it) 
  done 

transpile_define btree_balR': btree_balR_def
transpile_prove btree_balR' btree_balR

transpile_define btree_balL': btree_balL_def
transpile_prove btree_balL' btree_balL

transpile_define btree_combine': btree_combine.simps
transpile_prove btree_combine' btree_combine 

transpile_define rbt_del': rbt_del.simps
transpile_prove rbt_del' rbt_del

transpile_define rbt_delete': rbt_delete_def
transpile_prove rbt_delete' rbt_delete

lemma rbt_delete'_HT:  "<rbt_map_assn_flat M b> 
     rbt_delete' k b
     <rbt_map_assn_flat (delete_map k M)>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.rbt_delete'.correct_translate)
    apply(rule rbt_delete_rule)
      apply (simp add: forget_it)
      apply (simp add: forget_it) 
  done

transpile_define rbt_empty': RBTree_Impl.tree_empty_def
transpile_prove rbt_empty' RBTree_Impl.tree_empty 
 
theorem rbt_empty'_rule:
  "<emp> rbt_empty' <rbt_map_assn_flat empty_map>"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.rbt_empty'.correct_translate)
    apply(rule rbt_empty_rule)
      apply (simp add: forget_it)
      apply (simp add: forget_it) 
  done


definition "rbt_empty_int_set == rbt_empty' :: (int, unit) rbt_node ref option Heap"
definition "rbt_insert_int_set k b \<equiv> rbt_insert' (k::int) () b"
definition "rbt_search_int_set \<equiv> rbt_search' :: int  \<Rightarrow> (int, unit) btree \<Rightarrow> unit option Heap" 
definition "rbt_delete_int_set \<equiv> rbt_delete' :: int  \<Rightarrow> (int, unit) btree \<Rightarrow> (int, unit) btree Heap_Monad.Heap "

export_code integer_of_int int_of_integer 
  rbt_empty_int_set rbt_insert_int_set rbt_search_int_set rbt_delete_int_set
  in SML module_name RBT

section "Example -- Skew Heap" 
fun btree_flat :: "'a::heap tree \<Rightarrow> 'a node ref option \<Rightarrow> Assertions.assn" where
  "btree_flat Tree.Leaf p = \<up>(p = None)"
| "btree_flat \<langle>lt, v, rt\<rangle> (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Tree_Impl.Node lp v rp * btree_flat lt lp * btree_flat rt rp)"
| "btree_flat \<langle>lt, v, rt\<rangle> None = false"

lemma forget_btree: "forget (Tree_Impl.btree t p) = (btree_flat t p)"
  apply(induct t arbitrary: p) apply (auto simp: forget_it)
  subgoal for t1 x2 t2 p apply(cases p)  by (auto simp: forget_it) 
  done
 

schematic_goal forget_skew_heap_mset: "forget (skew_heap_mset T b) = ?G"
  unfolding skew_heap_mset_def skew_heap_def
  apply (subst forget_it forget_btree)+
  by (rule refl)
concrete_definition skew_heap_mset_flat uses forget_skew_heap_mset
print_theorems
lemmas [forget_it] =  skew_heap_mset_flat.refine 

transpile_define skew_heap_merge_impl': merge_impl.simps
transpile_prove skew_heap_merge_impl' merge_impl

lemma skew_heap_merge'_rule:
  "<skew_heap_mset_flat S a * skew_heap_mset_flat T b>
    skew_heap_merge_impl' a b
   <skew_heap_mset_flat (S + T)>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.skew_heap_merge_impl'.correct_translate)
    apply(rule skew_heap_merge_rule)
   apply (simp add: forget_it) 
  apply (simp add: forget_it) 
  done

transpile_define skew_heap_constr': skew_heap_constr_def[unfolded tree_constr_def]
transpile_prove skew_heap_constr' skew_heap_constr 


transpile_define skew_heap_insert_impl': insert_impl_def
transpile_prove skew_heap_insert_impl'  insert_impl  
 
lemma skew_heap_insert_impl'_rule:
  "<skew_heap_mset_flat S a >
    skew_heap_insert_impl' x a
   <skew_heap_mset_flat ({#x#} + S)>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.skew_heap_insert_impl'.correct_translate)
    apply(rule skew_heap_insert_rule)
      apply (simp add: forget_it)
      apply (simp add: forget_it) 
  done

transpile_define skew_heap_del_min_impl': del_min_impl.simps
transpile_prove skew_heap_del_min_impl' del_min_impl

lemma skew_heap_del_min_rule'_rule:
  "S \<noteq> {#} \<Longrightarrow><skew_heap_mset_flat S a>
    skew_heap_del_min_impl'  a
   <skew_heap_mset_flat (S - {# Min_mset S #}) >\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.skew_heap_del_min_impl'.correct_translate)
    apply(rule skew_heap_del_min_rule)
    apply simp
   apply (simp add: forget_it)
  apply (simp add: forget_it) 
  done

term skew_heap_empty
thm skew_heap_empty_rule''


transpile_define skew_heap_empty': skew_heap_empty_def[unfolded Tree_Impl.tree_empty_def]
transpile_prove skew_heap_empty' skew_heap_empty  

lemma "<emp> skew_heap_empty' <skew_heap_mset_flat {#}>\<^sub>t"
  apply(rule refines_HT) 
     apply(rule Transpile_Tests.skew_heap_empty'.correct_translate)
    apply(rule skew_heap_empty_rule'') 
   apply (simp add: forget_it)
  apply (simp add: forget_it) 
  done

export_code skew_heap_empty' skew_heap_insert_impl'
          skew_heap_del_min_impl' skew_heap_insert_impl' in SML

section "Examples -- with fixp combinator"


subsection \<open>Remove Duplicates\<close>

lemma [transpile_rules]:   "refines (return v) (ureturn v)"
  unfolding refines_def return_def ureturn_def
    Heap_Time_Monad.effect_def Heap_Monad.effect_def
    Heap_Time_Monad.heap_def Heap_Monad.heap_def
  by auto

lemma [transpile_rules]:   "
  (\<And>a b. refines (f' a b) (f a b)) \<Longrightarrow>
  refines (case x of (a,b) \<Rightarrow> f' a b) (case x of (a,b) \<Rightarrow> f a b)"
  by (auto split: prod.splits)

transpile_define set_empty': set_empty_def
transpile_prove set_empty' set_empty

transpile_define rbt_mem': rbt_mem_def
transpile_prove rbt_mem' rbt_mem

transpile_define rbt_set_insert': rbt_set_insert_def
transpile_prove rbt_set_insert' rbt_set_insert

transpile_define remdups_impl': remdups_impl_def[unfolded heap_WHILET_def, THEN meta_eq_to_obj_eq]
transpile_prove  remdups_impl' remdups_impl
print_theorems

lemmas [code del] = remdups_impl'_def
thm remdups_impl'_def[unfolded to_meta_eq, unfolded   ]
prepare_code_thms remdups_impl'_def[unfolded to_meta_eq, unfolded   ]
 
definition remdups_impl'_nat :: "nat list \<Rightarrow> nat dynamic_array Heap_Monad.Heap" where
  "remdups_impl'_nat as \<equiv>remdups_impl' as"                 
prepare_code_thms remdups_impl'_nat_def[unfolded remdups_impl'_def]
 
export_code remdups_impl'_nat in SML module_name REMDUPS


subsection \<open>Kruskal\<close>


term kruskal'
thm kruskal'_def

term kruskal_final
thm kruskal_final_def

thm Kruskal_Time.Kruskal_final.E

term Kruskal_intermediate_Impl.kruskal


lemma list_case_reines[transpile_rules]:
    "refines f' f 
    \<Longrightarrow> (\<And>x xs. refines (g' x xs) (g x xs))
    \<Longrightarrow>  refines (case x of [] \<Rightarrow> f' | (x#xs) \<Rightarrow> g' x xs)
         (case x of [] \<Rightarrow> f | (x#xs) \<Rightarrow> g x xs)"
  by (auto split: list.splits)



lemma case_wrap_refine[transpile_rules]:
  "(\<And>a. refines (f' a) (f a)) \<Longrightarrow> refines (case_wrap f' x) (case_wrap f x)"
  by(auto split: wrap.splits)

transpile_define maxn'': maxn'.simps
transpile_replay maxn'' maxn'
transpile_prove maxn'' maxn'

transpile_define maxn': maxn_def
transpile_prove maxn' maxn

transpile_define sortEdges'': sortEdges'_def
transpile_prove sortEdges'' sortEdges'

thm uf_init_def
transpile_define uf_init': uf_init_def[THEN meta_eq_to_obj_eq]
transpile_prove uf_init' uf_init

transpile_define uf_rep_of': uf_rep_of.simps
transpile_prove uf_rep_of' uf_rep_of 

transpile_define uf_compress': uf_compress.simps
transpile_prove uf_compress' uf_compress 

transpile_define uf_rep_of_c': uf_rep_of_c_def[THEN meta_eq_to_obj_eq]
transpile_prove uf_rep_of_c' uf_rep_of_c

transpile_define uf_cmp': uf_cmp_def[THEN meta_eq_to_obj_eq]
transpile_prove uf_cmp' uf_cmp

transpile_define uf_union' : uf_union_def[THEN meta_eq_to_obj_eq]
transpile_prove uf_union' uf_union
 
thm  kruskal_final_def[of getEdges_impl]
definition "kruskal_final_final as = kruskal_final (Heap_Time_Monad.return as)"
thm kruskal_final_final_def[unfolded kruskal_final_def kruskal'_def]
transpile_define kruskal_final': kruskal_final_final_def[unfolded kruskal_final_def kruskal'_def]
transpile_prove kruskal_final' kruskal_final

thm kruskal_final'_def
definition "Kruskal_fun as \<equiv> do { k \<leftarrow> kruskal_final' as; a \<leftarrow> destroy' k; Array.freeze a}"
prepare_code_thms (in -) Kruskal_fun_def[unfolded kruskal_final'_def]
print_theorems
 
export_code integer_of_int int_of_integer
    integer_of_nat  nat_of_integer
    Kruskal_fun in SML module_name KRUSKAL
 
subsection \<open>Floyd-Warshall\<close>


lemma "(\<And>x. f x = g x) \<Longrightarrow> f = g" apply (rule ext) by simp
lemma kl: "f = g \<Longrightarrow> (\<And>x. f x = g x)"  
  by auto

transpile_define mtx_get': mtx_get_def
transpile_prove mtx_get' mtx_get

transpile_define mtx_set': mtx_set_def
transpile_prove mtx_set' mtx_set

term fw_upd_impl
thm fw_upd_impl_def
transpile_define fw_upd_impl': fw_upd_impl_def[THEN meta_eq_to_obj_eq, 
    THEN kl, THEN kl, THEN kl, THEN kl, unfolded PR_CONST_def]
transpile_prove fw_upd_impl' fw_upd_impl


term fw_impl
thm fw_impl_def
thm fw_impl_def[THEN meta_eq_to_obj_eq]
transpile_define fw_impl': fw_impl_def[THEN meta_eq_to_obj_eq, THEN kl ]
transpile_prove fw_impl' fw_impl
lemmas [code del] = fw_impl'_def
thm fw_impl'_def
prepare_code_thms fw_impl'_def[unfolded to_meta_eq] 
print_theorems

subsection "Edmonds Karp"



thm Network_Impl.edka_imp_correct
term edka_imp

thm refines_imp_for

transpile_define mtx_tabulate': mtx_tabulate_def[THEN meta_eq_to_obj_eq]
transpile_prove mtx_tabulate' mtx_tabulate

transpile_define init_cf_impl': init_cf_impl_def[THEN meta_eq_to_obj_eq]
transpile_prove init_cf_impl' init_cf_impl

transpile_define edka_imp_tabulate': edka_imp_tabulate_def[THEN meta_eq_to_obj_eq]
transpile_prove edka_imp_tabulate' edka_imp_tabulate

transpile_define new_liam': new_liam_def
transpile_prove new_liam' new_liam

transpile_define update_liam': update_liam_def
transpile_prove update_liam' new_liam

transpile_define nth_liam': nth_liam_def
transpile_prove nth_liam' nth_liam

transpile_define dom_member_liam': dom_member_liam_def
transpile_prove dom_member_liam' dom_member_liam

transpile_define os_empty': os_empty_def
transpile_prove os_empty' os_empty

transpile_define os_prepend': os_prepend_def
transpile_prove os_prepend' os_prepend

transpile_define os_pop': os_pop_def
transpile_prove os_pop' os_pop

transpile_define list_set_pick_extract': list_set_pick_extract_def[ THEN kl ]
transpile_prove list_set_pick_extract' list_set_pick_extract

transpile_define list_set_empty': list_set_empty_def
transpile_prove list_set_empty' list_set_empty

transpile_define list_set_insert': list_set_insert_def
transpile_prove list_set_insert' list_set_insert

transpile_define list_set_isempty': list_set_isempty_def[unfolded os_is_empty_def, THEN kl ]
transpile_prove list_set_isempty' list_set_isempty

transpile_define init_state_impl': init_state_impl_def[THEN meta_eq_to_obj_eq]
transpile_prove init_state_impl' init_state_impl

transpile_define oappend': oappend_def
transpile_prove oappend' oappend

 
transpile_define bfs_impl': bfs_impl_def[THEN meta_eq_to_obj_eq]
thm bfs_impl'_def
print_theorems
transpile_prove bfs_impl' bfs_impl
print_theorems
lemmas [code del] = bfs_impl'_def
prepare_code_thms bfs_impl'_def[unfolded to_meta_eq] 

transpile_define ps_get_imp': ps_get_imp_def[THEN meta_eq_to_obj_eq]
transpile_prove ps_get_imp' ps_get_imp
thm succ_imp_def
transpile_define succ_imp': succ_imp_def[THEN meta_eq_to_obj_eq, unfolded PR_CONST_def]
transpile_prove succ_imp' succ_imp
lemmas [code del] = succ_imp'_def
prepare_code_thms succ_imp'_def[unfolded to_meta_eq] 
thm succ_imp'_def
 
transpile_define bfsi'': bfsi'_def[THEN meta_eq_to_obj_eq, unfolded split_beta']
transpile_prove bfsi'' bfsi'
thm bfsi''_def

transpile_define resCap_imp': resCap_imp_def[THEN meta_eq_to_obj_eq, unfolded PR_CONST_def]
transpile_prove resCap_imp' resCap_imp
lemmas [code del] = resCap_imp'_def
prepare_code_thms resCap_imp'_def[unfolded to_meta_eq] 

transpile_define augment_imp': augment_imp_def[THEN meta_eq_to_obj_eq, THEN kl,THEN kl,THEN kl,unfolded PR_CONST_def]
transpile_prove augment_imp' augment_imp
lemmas [code del] = augment_imp'_def
prepare_code_thms augment_imp'_def[unfolded to_meta_eq] 


transpile_define edka_imp_run': edka_imp_run_def[THEN meta_eq_to_obj_eq]
transpile_prove edka_imp_run' edka_imp_run
lemmas [code del] = edka_imp_run'_def
prepare_code_thms edka_imp_run'_def[unfolded to_meta_eq] 

transpile_define edka_imp': edka_imp_def[THEN meta_eq_to_obj_eq]
transpile_prove edka_imp' edka_imp
thm edka_imp'_def

lemmas [code] = imp_for''.simps

definition "edka c s t N am = do {
          res \<leftarrow> edka_imp c s t N am;
          r \<leftarrow> Array_Time.freeze res;
          Heap_Time_Monad.return (r, length r)}"

transpile_define  edka': edka_def
transpile_prove  edka' edka
 

export_code integer_of_int int_of_integer
    integer_of_nat  nat_of_integer
 edka' in SML module_name EDKA

section "partial_function strangeness"

thm rbt_ins.raw_induct (* no tuple *)
thm btree_combine.raw_induct (* no tuple *)
thm binarysearch.raw_induct (* tuple *)
thm rbt_search.raw_induct (* tuple *)
thm rbt_del.raw_induct (* tuple *)

partial_function (heap_time) rbt_del2 ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap_Time_Monad.Heap" where
  "rbt_del2 x p = (case p of
     None \<Rightarrow> Heap_Time_Monad.return None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;rbt_del2 x (RBTree_Impl.lsub t)})"
thm rbt_del2.raw_induct (* tuple *)

end