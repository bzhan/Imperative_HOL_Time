theory Transpile_Tests_Sepref
imports 
  Transpile_Tests
 "SeprefTime.Remdups" "SeprefTime.Kruskal_Time" 
 "SeprefTime.FW_Code" "SeprefTime.EdmondsKarp_Time"
 "HOL-Library.Code_Target_Numeral"
begin

section "Examples -- with fixp combinator"

subsection \<open>Remove Duplicates\<close>

lemma [transpile_rules]:   "refines (return v) (ureturn v)"
  unfolding refines_def return_def ureturn_def
    Heap_Time_Monad.effect_def Heap_Monad.effect_def
    Heap_Time_Monad.heap_def Heap_Monad.heap_def
  by auto

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

lemma list_case_refines[transpile_rules]:
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

transpile_define fw_upd_impl': fw_upd_impl_def[THEN meta_eq_to_obj_eq, 
    THEN kl, THEN kl, THEN kl, THEN kl, unfolded PR_CONST_def]
transpile_prove fw_upd_impl' fw_upd_impl

transpile_define fw_impl': fw_impl_def[THEN meta_eq_to_obj_eq, THEN kl ]
transpile_prove fw_impl' fw_impl
lemmas [code del] = fw_impl'_def

prepare_code_thms fw_impl'_def[unfolded to_meta_eq] 


subsection "Edmonds Karp"

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
transpile_prove bfs_impl' bfs_impl
lemmas [code del] = bfs_impl'_def
prepare_code_thms bfs_impl'_def[unfolded to_meta_eq] 

transpile_define ps_get_imp': ps_get_imp_def[THEN meta_eq_to_obj_eq]
transpile_prove ps_get_imp' ps_get_imp

transpile_define succ_imp': succ_imp_def[THEN meta_eq_to_obj_eq, unfolded PR_CONST_def]
transpile_prove succ_imp' succ_imp
lemmas [code del] = succ_imp'_def
prepare_code_thms succ_imp'_def[unfolded to_meta_eq] 
 
transpile_define bfsi'': bfsi'_def[THEN meta_eq_to_obj_eq, unfolded split_beta']
transpile_prove bfsi'' bfsi'

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