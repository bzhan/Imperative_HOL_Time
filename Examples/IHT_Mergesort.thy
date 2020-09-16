theory IHT_Mergesort
  imports "../Functional/MergeSort" IHT_Arrays
begin

section \<open>Imperative version\<close>

function mergeinto :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{heap,linorder} array \<Rightarrow> 'a array \<Rightarrow> 'a array \<Rightarrow> unit Heap" where
  "mergeinto 0 0 a b c = return ()"
| "mergeinto (Suc la) 0 a b c = do {
     mergeinto la 0 a b c;
     e \<leftarrow> Array_Time.nth a la;
     Array_Time.upd la e c;
     return ()
   }"
| "mergeinto 0 (Suc lb) a b c = do {
     mergeinto 0 lb a b c;
     e \<leftarrow> Array_Time.nth b lb;
     Array_Time.upd lb e c;
     return ()
   }"
| "mergeinto (Suc la) (Suc lb) a b c = do {
     ha \<leftarrow> Array_Time.nth a la;
     hb \<leftarrow> Array_Time.nth b lb;
     if ha \<ge> hb then do {
       mergeinto la (Suc lb) a b c;
       Array_Time.upd (Suc (la+lb)) ha c;
       return ()
     }
     else do {
       mergeinto (Suc la) lb a b c;
       Array_Time.upd (Suc (la+lb)) hb c;
       return ()
     }
   }"
by pat_completeness auto
termination by (relation "Wellfounded.measure (\<lambda>(la, lb, a, b, c). la + lb)") auto

lemma mergeinto_to_fun [hoare_triple]:
  "la \<le> length as \<Longrightarrow> lb \<le> length bs \<Longrightarrow> length cs = length as + length bs \<Longrightarrow>
    <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a cs * $(4 * (la + lb) + 2)>
    mergeinto la lb a b c
    <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a mergeinto_fun la lb as bs cs>\<^sub>t"
@proof @fun_induct "mergeinto_fun la lb as bs cs" @with
  @subgoal "(la = Suc la, lb = Suc lb, as = as, bs = bs, cs = cs)"
    @case "bs ! lb \<le> as ! la"
  @endgoal @end
@qed

definition mergeinto_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "mergeinto_time n = 4 * n + 2"

lemma mergeinto_correct [hoare_triple]:
  "length as = la \<Longrightarrow> length bs = lb \<Longrightarrow> length cs = la + lb \<Longrightarrow>
    <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a cs * $(mergeinto_time (length cs))>
    mergeinto la lb a b c
    <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a MergeSort.merge_list as bs>\<^sub>t"
@proof @have "mergeinto_time (length cs) \<ge>\<^sub>t 4 * (la + lb) + 2" @qed  (* TODO: why need this? *)

lemma mergeinto_time_bound [asym_bound]: "(\<lambda>n. mergeinto_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: mergeinto_time_def) auto2

setup \<open>del_prfstep_thm @{thm mergeinto_time_def}\<close>

partial_function (heap_time) merge_sort_impl :: "'a::{heap,linorder} array \<Rightarrow> unit Heap" where
  "merge_sort_impl X = do {
    n \<leftarrow> Array_Time.len X;
    if n \<le> 1 then return ()
    else do { 
      A \<leftarrow> atake (n div 2) X;
      B \<leftarrow> adrop (n div 2) X;
      merge_sort_impl A;
      merge_sort_impl B;
      mergeinto (n div 2) (n - n div 2) A B X
    }
  }"

function merge_sort_time :: "nat \<Rightarrow> nat" where
  "n \<le> 1 \<Longrightarrow> merge_sort_time n = 2"
| "n > 1 \<Longrightarrow> merge_sort_time n =
    atake_time n + adrop_time n + mergeinto_time n + 1 +
    (merge_sort_time (n div 2) + merge_sort_time (n - n div 2))"
  by force simp_all
  termination by (relation "Wellfounded.measure (\<lambda>n. n)") auto
setup \<open>fold add_rewrite_rule @{thms merge_sort_time.simps}\<close>

definition merge_sort_time' :: "nat \<Rightarrow> real" where
  "merge_sort_time' n = real (merge_sort_time n)"

lemma div_2_to_rounding:
  "n - n div 2 = nat \<lceil>n / 2\<rceil>" "n div 2 = nat \<lfloor>n / 2\<rfloor>" by linarith+

lemma merge_sort_time_O:
  "(\<lambda>n. merge_sort_time n) \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  unfolding merge_sort_time'_def[symmetric]
  apply (master_theorem2 2.3 recursion: merge_sort_time.simps(2)
         rew: merge_sort_time'_def div_2_to_rounding)
  apply (auto simp: merge_sort_time'_def div_2_to_rounding)
  by auto2

lemma mergeSort_to_fun [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * $(merge_sort_time (length xs))>
   merge_sort_impl p
   <\<lambda>_. p \<mapsto>\<^sub>a merge_sort_fun xs>\<^sub>t"
@proof
  @fun_induct "merge_sort_fun xs" arbitrary p
  @unfold "merge_sort_fun xs"
@qed

lemma mergeSort_correct [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * $(merge_sort_time (length xs))>
   merge_sort_impl p
   <\<lambda>_. p \<mapsto>\<^sub>a sort xs>\<^sub>t" by auto2

end
