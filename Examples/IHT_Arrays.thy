theory IHT_Arrays
  imports
    "../SepLogicTime/SLTC_Main"
    "../Asymptotics/Asymptotics_1D"
    Auto2_Imperative_HOL.Arrays_Ex
begin

definition acopy :: "'a::heap array \<Rightarrow> 'a array Heap" where
  "acopy a = do {
     as \<leftarrow> Array_Time.freeze a;
     Array_Time.of_list as
   }"

definition acopy_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "acopy_time n = 2 * n + 2"

lemma acopy_correct [hoare_triple]:
  "<a \<mapsto>\<^sub>a as * $(acopy_time (length as))>
   acopy a
   <\<lambda>r. a \<mapsto>\<^sub>a as * r \<mapsto>\<^sub>a as>" by auto2

lemma acopy_time_bound [asym_bound]:
  "(\<lambda>n. acopy_time n) \<in> \<Theta>(\<lambda>n. n)"
  apply (simp only: acopy_time_def) by auto2

setup \<open>del_prfstep_thm @{thm acopy_time_def}\<close>

fun array_copy :: "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_copy a b 0 = (return ())"
| "array_copy a b (Suc n) = do {
      array_copy a b n;
      x \<leftarrow> Array_Time.nth a n;
      Array_Time.upd n x b;
      return () }"

lemma array_copy_rule [hoare_triple]:
  "n \<le> length as \<Longrightarrow> n \<le> length bs \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(3*n+1)>
    array_copy a b n
   <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a Arrays_Ex.array_copy as bs n>"
@proof @induct n @qed

definition atake :: "nat \<Rightarrow> 'a::heap array \<Rightarrow> 'a array Heap" where
  "atake n xs = do {
     XS \<leftarrow> Array_Time.freeze xs;
     Array_Time.of_list (take n XS)
   }"

definition atake_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "atake_time n = 2*n + 2"

lemma atake_copies [hoare_triple]:
  "n \<le> length as \<Longrightarrow>
   <xs \<mapsto>\<^sub>a as * $(atake_time (length as))>
    atake n xs
   <\<lambda>r. r \<mapsto>\<^sub>a take n as * xs \<mapsto>\<^sub>a as>\<^sub>t"
@proof
  @have "length as + 1 \<ge>\<^sub>t n + 1"  (* TODO: why is this needed *)
@qed 

lemma atake_time_bound [asym_bound]:
  "(\<lambda>n. atake_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: atake_time_def) auto2

setup \<open>del_prfstep_thm @{thm atake_time_def}\<close>


definition adrop :: "nat \<Rightarrow> 'a::heap array \<Rightarrow> 'a array Heap" where
  "adrop n xs = do {
     XS \<leftarrow> Array_Time.freeze xs;
     Array_Time.of_list (drop n XS)
   }"

definition adrop_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "adrop_time n = 2*n + 2"

lemma adrop_copies [hoare_triple]:
  "n \<le> length as \<Longrightarrow>
   <xs \<mapsto>\<^sub>a as * $(adrop_time (length as))>
    adrop n xs
   <\<lambda>r. r \<mapsto>\<^sub>a drop n as * xs \<mapsto>\<^sub>a as>\<^sub>t"
@proof
  @have "length as + 1 \<ge>\<^sub>t (length as - n) + 1"
  @qed

lemma adrop_time_bound [asym_bound]:
  "(\<lambda>n. adrop_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: adrop_time_def) auto2

setup \<open>del_prfstep_thm @{thm adrop_time_def}\<close>

definition asplit :: "'a::heap array \<Rightarrow> nat \<Rightarrow> ('a array \<times> 'a array) Heap" where
  "asplit a n = do {
     b \<leftarrow> atake n a;
     c \<leftarrow> adrop n a;
     return (b, c)
   }"

definition asplit_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "asplit_time la = atake_time la + adrop_time la + 1"

lemma asplit_correct [hoare_triple]:
  "n \<le> length as \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * $(asplit_time (length as))>
   asplit a n
   <\<lambda>(p,q). a \<mapsto>\<^sub>a as * p \<mapsto>\<^sub>a take n as * q \<mapsto>\<^sub>a drop n as>\<^sub>t"
@proof
  @have "length as \<ge>\<^sub>t n + (length as - n)"
@qed

lemma asplit_time_bound [asym_bound]:
  "(\<lambda>n. asplit_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: asplit_time_def) auto2

setup \<open>del_prfstep_thm @{thm asplit_time_def}\<close>

end
