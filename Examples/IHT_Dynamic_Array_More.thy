theory IHT_Dynamic_Array_More
imports IHT_Dynamic_Array "../Asymptotics/Asymptotics_1D"
begin

fun dyn_array_P' :: "'a::heap list \<times> nat \<Rightarrow> nat" where
  "dyn_array_P' (xs, n) = 4 * n"
setup \<open>add_rewrite_rule @{thm dyn_array_P'.simps}\<close>

lemma dyn_array_new_P' [rewrite]:
  "dyn_array_P' (replicate 5 0, 0) = 0" by auto2

lemma dyn_array_double_length_P' [rewrite]:
  "dyn_array_P' (double_length_fun (xs, n)) = dyn_array_P' (xs, n)" by auto2

lemma dyn_array_push_array_basic_P' [resolve]:
  "n \<le> length xs \<Longrightarrow>
   dyn_array_P' (xs, n) + 16 \<ge>\<^sub>t dyn_array_P' (push_array_basic_fun x (xs, n)) + 12" by auto2

lemma update_P' [rewrite]:
  "i < n \<Longrightarrow> dyn_array_P' (list_update xs i x, n) = dyn_array_P' (xs, n)" by auto2

lemma dyn_array_destroy_P' [resolve]:
  "dyn_array_P' (xs, n) + 3 \<ge>\<^sub>t 4 * n + 3" by auto2

setup \<open>del_prfstep_thm @{thm dyn_array_P'.simps}\<close>

fun dyn_array'' :: "'a::heap list \<times> nat \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where
  "dyn_array'' (xs, n) r = dyn_array' (xs, n) r * $(dyn_array_P' (xs, n))"
setup \<open>add_rewrite_ent_rule @{thm dyn_array''.simps}\<close>

lemma dyn_array_new_rule'' [hoare_triple]:
  "<$7>
   dyn_array_new
   <dyn_array'' (replicate 5 0, 0)>\<^sub>t"
@proof
  @have "7 \<ge>\<^sub>t 7 + dyn_array_P' (replicate 5 0, 0)"
@qed

lemma double_length_rule'' [hoare_triple]:
  "length xs = n \<Longrightarrow>
   <dyn_array'' (xs, n) p * $5>
   double_length p
   <dyn_array'' (double_length_fun (xs, n))>\<^sub>t"
@proof
  @have "dyn_array_P' (xs, n) + 5 \<ge>\<^sub>t dyn_array_P' (double_length_fun (xs, n)) + 5"
@qed

lemma push_array_basic_rule'' [hoare_triple]:
  "n < length xs \<Longrightarrow>
   <dyn_array'' (xs, n) p * $16>
    push_array_basic x p
   <dyn_array'' (list_update xs n x, n + 1)>\<^sub>t"
@proof
  @have "dyn_array_P' (xs, n) + 16 \<ge>\<^sub>t dyn_array_P' (push_array_basic_fun x (xs, n)) + 12"
@qed
 
lemma array_length_rule'' [hoare_triple]:
  "<dyn_array'' (xs, n) p * $1>
   array_length p
   <\<lambda>r. dyn_array'' (xs, n) p * \<up>(r = n)>" by auto2

lemma array_max_rule'' [hoare_triple]:
  "<dyn_array'' (xs, n) p * $1>
   array_max p
   <\<lambda>r. dyn_array'' (xs, n) p * \<up>(r = length xs)>" by auto2

lemma array_nth_rule'' [hoare_triple]:
  "i < n \<Longrightarrow> n \<le> length xs \<Longrightarrow>
   <dyn_array'' (xs, n) p * $1>
   array_nth p i
   <\<lambda>r. dyn_array'' (xs, n) p * \<up>(r = xs ! i)>" by auto2

lemma array_upd_rule'' [hoare_triple]:
  "i < n \<Longrightarrow> n \<le> length xs \<Longrightarrow>
   <dyn_array'' (xs, n) p * $2>
   array_upd i x p
   <\<lambda>_. dyn_array'' (list_update xs i x, n) p>" by auto2

lemma destroy_rule'' [hoare_triple]:
  "n \<le> length xs \<Longrightarrow>
   <dyn_array'' (xs, n) d * $3>
   destroy d
   <\<lambda>r. r \<mapsto>\<^sub>a take n xs>\<^sub>t"
@proof 
  @have "dyn_array_P' (xs, n) + 3 \<ge>\<^sub>t 4 * n + 3"
@qed

setup \<open>del_prfstep_thm @{thm dyn_array''.simps}\<close>

section \<open>Derived operations\<close>

lemma push_array_rule'' [hoare_triple]:
  "n \<le> length xs \<Longrightarrow>
   <dyn_array'' (xs, n) p * $23>
   push_array x p
   <dyn_array'' (push_array_fun x (xs, n))>\<^sub>t" by auto2

section \<open>Abstract assertion\<close>

fun abs_array :: "'a::heap list \<times> nat \<Rightarrow> 'a list" where
  "abs_array (xs, n) = take n xs"
setup \<open>add_rewrite_rule @{thm abs_array.simps}\<close>

lemma double_length_abs [rewrite]:
  "length xs = n \<Longrightarrow> abs_array (double_length_fun (xs, n)) = abs_array (xs, n)" by auto2

lemma push_array_basic_abs [rewrite]:
  "n < length xs \<Longrightarrow> abs_array (push_array_basic_fun x (xs, n)) = abs_array (xs, n) @ [x]"
@proof @have "length (take n xs @ [x]) = n + 1" @qed

lemma push_array_fun_abs [rewrite]:
  "n \<le> length xs \<Longrightarrow> abs_array (push_array_fun x (xs, n)) = abs_array (xs, n) @ [x]" by auto2

definition dyn_array :: "'a::heap list \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where [rewrite_ent]:
  "dyn_array xs a = (\<exists>\<^sub>Ap. dyn_array'' p a * \<up>(snd p \<le> length (fst p)) * \<up>(xs = abs_array p))"

lemma dyn_array_new_rule [hoare_triple]:
  "<$7>
   dyn_array_new
   <dyn_array []>\<^sub>t" by auto2

lemma array_length_rule [hoare_triple]:
  "<dyn_array xs p * $1>
    array_length p
   <\<lambda>r. dyn_array xs p * \<up>(r = length xs)>" by auto2

lemma array_nth_rule [hoare_triple]:
  "i < length xs \<Longrightarrow>
   <dyn_array xs p * $1>
    array_nth p i
   <\<lambda>r. dyn_array xs p * \<up>(r = xs ! i)>" by auto2

lemma array_upd_rule [hoare_triple]:
  "i < length xs \<Longrightarrow>
   <dyn_array xs p * $2>
    array_upd i x p
   <\<lambda>_. dyn_array (list_update xs i x) p>" by auto2

lemma push_array_rule [hoare_triple]:
  "<dyn_array xs p * $23>
    push_array x p
   <dyn_array (xs @ [x])>\<^sub>t" by auto2

lemma destroy_rule [hoare_triple]:
  "<dyn_array xs p * $3>
    destroy p
   <\<lambda>r. r \<mapsto>\<^sub>a xs>\<^sub>t" by auto2

setup \<open>del_simple_datatype "dynamic_array"\<close>
setup \<open>del_prfstep_thm @{thm dyn_array_def}\<close>

section \<open>More operations\<close>

definition array_swap :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_swap d i j = do {
    x \<leftarrow> array_nth d i;
    y \<leftarrow> array_nth d j;
    array_upd i y d;
    array_upd j x d;
    return ()
   }"

lemma array_swap_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   <dyn_array xs p * $7>
   array_swap p i j
   <\<lambda>_. dyn_array (list_swap xs i j) p>" by auto2

text \<open>Filter with dynamic array\<close>

fun dfilter_aux_fun :: "'a list \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list" where
  "dfilter_aux_fun xs 0 P = []"
| "dfilter_aux_fun xs (Suc n) P = (
     if P (xs ! n)
     then dfilter_aux_fun xs n P @ [xs ! n]
     else dfilter_aux_fun xs n P)"
setup \<open>fold add_rewrite_rule @{thms dfilter_aux_fun.simps}\<close>

lemma dfilter_aux_fun_ind [rewrite]:
  "i \<le> length xs \<Longrightarrow> dfilter_aux_fun xs i P = filter P (take i xs)"        
  by (induct i) (auto simp add: take_Suc_conv_app_nth)
 
lemma filtertake_Suc [rewrite]:
  "i < length xs \<Longrightarrow> P (xs !i) \<Longrightarrow> filter P (take (Suc i) xs) = filter P (take i xs) @ [xs ! i]"
  "i < length xs \<Longrightarrow> ~ P (xs !i) \<Longrightarrow> filter P (take (Suc i) xs) = filter P (take i xs)"
  by (auto simp add: take_Suc_conv_app_nth) 

fun dfilter_aux :: "('a::{zero,heap}) array \<Rightarrow> 'a dynamic_array \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a dynamic_array Heap" where
  "dfilter_aux a d 0 P = return d"
| "dfilter_aux a d (Suc i) P = do {
     d' \<leftarrow> dfilter_aux a d i P;
     x \<leftarrow> Array_Time.nth a i;
     if P x then push_array x d' else return d'
   }"

lemma dfilter_aux_rule [hoare_triple]:
  "i \<le> length xs \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs * dyn_array [] d * $(i * 24 + 1)>
    dfilter_aux a d i P
   <\<lambda>r. a \<mapsto>\<^sub>a xs * dyn_array (filter P (take i xs)) r>\<^sub>t"
@proof @induct i @qed

definition dfilter_impl :: "'a::{zero,heap} array \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a dynamic_array Heap" where
  "dfilter_impl a P = do {
     d \<leftarrow> dyn_array_new;
     alen \<leftarrow> Array_Time.len a;
     dfilter_aux a d alen P
   }" 

definition dfilter_impl_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "dfilter_impl_time l = 8 + 1 + (24 * l + 1)"

lemma dfilter_impl_rule[hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * $(dfilter_impl_time (length xs))>
    dfilter_impl a P  
   <\<lambda>r. a \<mapsto>\<^sub>a xs * dyn_array (filter P xs) r>\<^sub>t" by auto2

lemma dfilter_impl_time_bound [asym_bound]: "(\<lambda>n. dfilter_impl_time n) \<in> \<Theta>(\<lambda>n. n)"
  unfolding dfilter_impl_time_def by auto2

setup \<open>del_prfstep_thm @{thm dfilter_impl_time_def}\<close>

end
