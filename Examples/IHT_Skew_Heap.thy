theory IHT_Skew_Heap
  imports 
    IHT_Tree
    Amortized_Complexity.Skew_Heap_Analysis
    "../Asymptotics/Asymptotics_1D"
begin

section \<open>Operations\<close>

partial_function (heap_time) merge_impl :: "'a::{heap,linorder} ptree \<Rightarrow> 'a ptree \<Rightarrow> 'a ptree Heap" where
  "merge_impl a b = (case a of
    None \<Rightarrow> return b
  | Some p \<Rightarrow> (case b of
      None \<Rightarrow> return a
    | Some q \<Rightarrow> do {
        ta \<leftarrow> !p;
        tb \<leftarrow> !q;
        (if val ta \<le> val tb then do {
           q' \<leftarrow> merge_impl (Some q) (rsub ta);
           p := Node q' (val ta) (lsub ta);
           return (Some p) }
         else do {
           p' \<leftarrow> merge_impl (Some p) (rsub tb);
           q := Node p' (val tb) (lsub tb);
           return (Some q) })}))"

setup \<open>fold add_rewrite_rule @{thms Skew_Heap.merge.simps}\<close>

definition merge_time :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> nat" where
  "merge_time t1 t2 = 4 * t_merge t1 t2"

lemma merge_time_simps [rewrite]:
  "merge_time Leaf h = 4"
  "merge_time h Leaf = 4"
  "merge_time \<langle>l1, a1, r1\<rangle> \<langle>l2, a2, r2\<rangle> =
     (if a1 \<le> a2 then merge_time \<langle>l2, a2, r2\<rangle> r1 else merge_time \<langle>l1, a1, r1\<rangle> r2) + 4"
  by (simp add: merge_time_def)+

lemma skew_heap_merge_correct [hoare_triple]:
  "<btree t1 a * btree t2 b * $(merge_time t1 t2)>
   merge_impl a b
   <btree (Skew_Heap.merge t1 t2)>\<^sub>t"
@proof @fun_induct "Skew_Heap.merge t1 t2" arbitrary a b @with
  @subgoal "(t1 = t1, t2 = Leaf)" @case "t1 = Leaf" @endgoal @end
@qed

definition "skew_heap_constr v = tree_constr v"

lemma skew_heap_constr_to_fun [hoare_triple]:
  "<$2> skew_heap_constr v <btree \<langle>Leaf, v, Leaf\<rangle>>\<^sub>t" by auto2

definition insert_impl :: "'a::{heap,linorder} \<Rightarrow> 'a ptree \<Rightarrow> 'a ptree Heap" where
  "insert_impl x t = do {
     s \<leftarrow> skew_heap_constr x;
     merge_impl s t
   }"

setup \<open>add_rewrite_rule @{thm Skew_Heap.insert_def}\<close>

partial_function (heap_time) del_min_impl :: "'a::{heap,linorder} ptree \<Rightarrow> 'a ptree Heap" where
  "del_min_impl a = (case a of
     None \<Rightarrow> return None
   | Some a \<Rightarrow> do {
      t \<leftarrow> !a;
      merge_impl (lsub t) (rsub t)
    })"

setup \<open>fold add_rewrite_rule @{thms Skew_Heap.del_min.simps}\<close>

fun del_min_time :: "'a::linorder tree \<Rightarrow> nat" where
  "del_min_time Leaf = 4"
| "del_min_time (tree.Node l v r) = merge_time l r + 4"
setup \<open>fold add_rewrite_rule @{thms del_min_time.simps}\<close>

lemma skew_heap_del_min_correct [hoare_triple]:
  "<btree t a * $(del_min_time t)>
    del_min_impl a
   <btree (del_min t)>\<^sub>t"
@proof @case "t = Leaf" @qed

section \<open>Amortized analysis\<close>

definition skew_heap_P :: "'a tree \<Rightarrow> nat" where [rewrite]:
  "skew_heap_P t = 4 * nat (\<Phi> t)"

definition skew_heap :: "'a::heap tree \<Rightarrow> 'a ptree \<Rightarrow> assn" where [rewrite_ent]:
  "skew_heap t a = btree t a * $(skew_heap_P t)"

definition merge_atime :: "nat \<Rightarrow> nat \<Rightarrow> nat" where [rewrite]:
  "merge_atime n1 n2 = 4 * nat (\<lceil>3 * log 2 (n1 + n2)\<rceil> + 1)"

lemma merge_P_rule [resolve]:
  "merge_time t1 t2 + skew_heap_P (Skew_Heap.merge t1 t2) \<le>
   skew_heap_P t1 + skew_heap_P t2 + merge_atime (size1 t1) (size1 t2)"
proof -
  have a_merge':
    "t_merge t1 t2 + nat (\<Phi> (Skew_Heap.merge t1 t2)) \<le>
     nat (\<Phi> t1) + nat (\<Phi> t2) + nat (\<lceil>3 * log 2 (real (size1 t1 + size1 t2))\<rceil> + 1)" (is "?lhs \<le> ?rhs")
  proof -
    have a_merge'': "real ?lhs \<le> real ?rhs"
    proof -
      have rhs_ge_zero: "\<lceil>3 * log 2 (size1 t1 + size1 t2)\<rceil> + 1 \<ge> 0" 
        by (smt Glog ceiling_mono ceiling_zero of_nat_0_le_iff of_nat_add zero_le_log_cancel_iff)
      have a_merge''': "real_of_int (int (t_merge t1 t2) + \<Phi> (Skew_Heap.merge t1 t2) - \<Phi> t1 - \<Phi> t2) \<le>
                        \<lceil>3 * log 2 (real (size1 t1 + size1 t2))\<rceil> + 1"
        using a_merge by (smt le_of_int_ceiling of_int_1 of_int_diff)
      show ?thesis
      apply (simp add: \<Phi>_nneg)
      apply (subst of_nat_nat)
        using rhs_ge_zero apply auto
        using a_merge''' by simp
    qed
    show ?thesis using a_merge'' of_nat_le_iff by blast
  qed
  show ?thesis
  apply (simp only: merge_time_def skew_heap_P_def merge_atime_def)
  using a_merge' by auto
qed

lemma skew_heap_merge_amor [hoare_triple]:
  "<skew_heap t1 a * skew_heap t2 b * $(merge_atime (size1 t1) (size1 t2))>
   merge_impl a b
   <skew_heap (Skew_Heap.merge t1 t2)>\<^sub>t"
@proof
  @have "skew_heap_P t1 + skew_heap_P t2 + merge_atime (size1 t1) (size1 t2) \<ge>\<^sub>t
         merge_time t1 t2 + skew_heap_P (Skew_Heap.merge t1 t2)"
@qed

lemma skew_heap_empty_P [rewrite]: "skew_heap_P Leaf = 0"
  by (simp add: skew_heap_P_def)

lemma skew_heap_constr_P [rewrite]: "skew_heap_P \<langle>Leaf, x, Leaf\<rangle> = 0"
  by (simp add: skew_heap_P_def rh_def)

definition "skew_heap_empty = tree_empty"

lemma skew_heap_empty_to_fun' [hoare_triple]:
  "<$1> skew_heap_empty <skew_heap Leaf>\<^sub>t"
@proof @have "1 \<ge>\<^sub>t 1 + skew_heap_P Leaf" @qed

lemma skew_heap_constr_to_fun' [hoare_triple]:
  "<$2> skew_heap_constr v <skew_heap \<langle>Leaf, v, Leaf\<rangle>>\<^sub>t"
@proof @have "2 \<ge>\<^sub>t 2 + skew_heap_P (tree.Node Leaf v Leaf)" @qed

definition del_min_atime :: "nat \<Rightarrow> nat" where
  "del_min_atime n = 4 * nat (\<lceil>3 * log 2 (n + 2)\<rceil> + 2)"

lemma del_min_time_rule:
  "del_min_time t = 4 * nat (t_del_min t)"
  by (induct t) (simp_all add: t_del_min_def merge_time_def)

lemma del_min_P_rule [resolve]:
  "del_min_time t + skew_heap_P (del_min t) \<le> skew_heap_P t + del_min_atime (size1 t)"
proof -
  have a_del_min':
    "nat (t_del_min t) + nat (\<Phi> (del_min t)) \<le>
     nat (\<Phi> t) + nat (\<lceil>3 * log 2 (real (size1 t + 2)) + 2\<rceil>)" (is "?lhs \<le> ?rhs")
  proof -
    have a_del_min'': "real ?lhs \<le> real ?rhs"
    proof -
      have rhs_ge_zero: "\<lceil>3 * log 2 (real (size1 t))\<rceil> + 2 \<ge> 0"
        by (smt Glog ceiling_mono ceiling_zero of_nat_0_le_iff)
      have a_del_min''': "real_of_int (t_del_min t + \<Phi> (del_min t) - \<Phi> t) \<le>
                          \<lceil>3 * log 2 (real (size1 t + 2))\<rceil> + 2"
        using a_del_min
        by (smt ceiling_diff_of_int le_of_int_ceiling of_int_1 of_int_minus)
      show ?thesis
        apply (simp add: \<Phi>_nneg)
        apply (subst of_nat_nat)
        using rhs_ge_zero t_del_min_def [of t] apply auto
        using a_del_min''' by simp
    qed
    show ?thesis using a_del_min'' of_nat_le_iff by blast
  qed
  show ?thesis
  apply (simp only: del_min_time_rule skew_heap_P_def del_min_atime_def)
    using a_del_min' by auto
qed

lemma skew_heap_del_min_to_fun' [hoare_triple]:
  "<skew_heap t a * $(del_min_atime (size1 t))>
    del_min_impl a
   <skew_heap (del_min t)>\<^sub>t"
@proof
  @have "skew_heap_P t + del_min_atime (size1 t) \<ge>\<^sub>t del_min_time t + skew_heap_P (del_min t)"
@qed

lemma del_min_atime_alt: "del_min_atime n = 8 + 4 * real (nat (\<lceil>3 * log 2 (2 + real n)\<rceil>))"
  apply (auto simp: del_min_atime_def) apply (subst nat_add_distrib)
  apply auto apply (rule less_le_trans[of _ 0]) using log2_gt_zero by auto

lemma del_min_atime_asym [asym_bound]:
  "(\<lambda>n. del_min_atime n) \<in> \<Theta>(\<lambda>n. ln (real n))"
  unfolding del_min_atime_alt 
  using abcd_lnx[of 8 4 3 2] by auto

setup \<open>del_prfstep_thm @{thm skew_heap_def}\<close>

definition insert_atime :: "nat \<Rightarrow> nat" where [rewrite]:
  "insert_atime n = merge_atime 2 n + 2"

lemma skew_heap_constr_size [rewrite]: "size1 \<langle>Leaf, x, Leaf\<rangle> = 2" by simp

lemma skew_heap_insert_to_fun' [hoare_triple]:
  "<skew_heap t a * $(insert_atime (size1 t))>
   insert_impl x a
   <skew_heap (Skew_Heap.insert x t)>\<^sub>t"
@proof
  @have "insert_atime (size1 t) \<ge>\<^sub>t merge_atime (size1 \<langle>Leaf, x, Leaf\<rangle>) (size1 t) + 2"
@qed

lemma insert_atime_alt: "insert_atime n = 6 + 4 * real (nat (\<lceil>3 * log 2 (real (2 + n))\<rceil>))"
  apply (auto simp: insert_atime_def merge_atime_def) apply(subst nat_add_distrib)
  apply auto apply(rule less_le_trans[of _ 0] ) using log2_gt_zero by auto

lemma insert_atime_asym [asym_bound]:
  "(\<lambda>n. insert_atime n) \<in> \<Theta>(\<lambda>x. ln (real x))"  (is "?f \<in> \<Theta>(?g)")
  unfolding insert_atime_alt by (rule abcd_lnx) auto

section \<open>Abstract assertion\<close>

definition skew_heap_mset :: "'a::{heap,linorder} multiset \<Rightarrow> 'a ptree \<Rightarrow> assn" where [rewrite_ent]:
  "skew_heap_mset S a = (\<exists>\<^sub>At. skew_heap t a * \<up>(heap t) * \<up>(mset_tree t = S))"

setup \<open>add_resolve_prfstep @{thm skew_heap.invar_empty}\<close>
setup \<open>fold add_rewrite_rule @{thms mset_tree.simps}\<close>

lemma size1_mset_tree [rewrite]:
  "size (mset_tree t) + 1 = size1 t" by (simp add: size1_size)

lemma skew_heap_empty_rule'' [hoare_triple]:
  "<$1> skew_heap_empty <skew_heap_mset {#}>\<^sub>t" by auto2

setup \<open>add_forward_prfstep @{thm Skew_Heap.heap_merge}\<close>
setup \<open>add_rewrite_rule @{thm Skew_Heap.mset_merge}\<close>
setup \<open>add_forward_prfstep @{thm Skew_Heap.heap_insert}\<close>
setup \<open>add_rewrite_rule @{thm Skew_Heap.mset_insert}\<close>
setup \<open>add_forward_prfstep @{thm Skew_Heap.heap_del_min}\<close>
setup \<open>add_rewrite_rule @{thm Skew_Heap.mset_del_min}\<close>

setup \<open>register_wellform_data ("get_min h", ["h \<noteq> Leaf"])\<close>
setup \<open>add_prfstep_check_req ("get_min h", "h \<noteq> Leaf")\<close>

setup \<open>add_rewrite_rule @{thm Skew_Heap.get_min}\<close>

lemma skew_heap_merge_rule [hoare_triple]:
  "<skew_heap_mset S a * skew_heap_mset T b * $(merge_atime (size S + 1) (size T + 1))>
    merge_impl a b
   <skew_heap_mset (S + T)>\<^sub>t" by auto2

lemma skew_heap_insert_rule [hoare_triple]:
  "<skew_heap_mset S a * $(insert_atime (size S + 1))>
    insert_impl x a
   <skew_heap_mset ({#x#} + S)>\<^sub>t" by auto2

lemma skew_heap_del_min_rule [hoare_triple]:
  "S \<noteq> {#} \<Longrightarrow>
   <skew_heap_mset S a * $(del_min_atime (size S + 1))>
    del_min_impl a
   <skew_heap_mset (S - {# Min_mset S #})>\<^sub>t" by auto2

end
