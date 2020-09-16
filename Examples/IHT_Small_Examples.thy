theory IHT_Small_Examples
  imports 
    "../SepLogicTime/SLTC_Main"
    "../Asymptotics/Asymptotics_1D"
begin

section \<open>f1 doubles\<close>

definition f1_impl :: "nat \<Rightarrow> nat Heap" where
  "f1_impl n = do { return (2*n) }"

definition f1_time :: nat where [rewrite]:
  "f1_time = 1"

lemma f1_time_bound [asym_bound]:
  "(\<lambda>n. f1_time) \<in> \<Theta>(\<lambda>(n::nat). 1)" unfolding f1_time_def by auto

lemma f1_rule [hoare_triple]:
  "<$(f1_time)> f1_impl n <\<lambda>r. \<up>(r=2*n)>\<^sub>t" by auto2

setup \<open>del_prfstep_thm @{thm f1_time_def}\<close>

section \<open>f2 builds two new Arrays\<close>

definition f2_impl :: "nat \<Rightarrow> ('a::heap array \<times> 'a array) Heap" where
  "f2_impl (n::nat) = do {
     r1 \<leftarrow> Array_Time.new n undefined;
     r2 \<leftarrow> Array_Time.new n undefined;
     return (r1,r2)
   }"

definition f2_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "f2_time n = 2 * n + 3"

lemma f2_time_bound [asym_bound]:
  "(\<lambda>n. f2_time n) \<in> \<Theta>(\<lambda>n. n)" unfolding f2_time_def by auto

lemma f2_rule [hoare_triple]:
  "<$(f2_time (n))>
    f2_impl n
   <\<lambda>r. fst r \<mapsto>\<^sub>a replicate n undefined * snd r \<mapsto>\<^sub>a replicate n undefined>\<^sub>t" by auto2
 
setup \<open>del_prfstep_thm @{thm f2_time_def}\<close>

section \<open>f squares the length of a list and generates two arrays of that size\<close>

definition f_impl :: "'a::heap list \<Rightarrow> ('a array \<times> 'a array) Heap" where
  "f_impl xs = do {
     n \<leftarrow> f1_impl (length xs);
     f2_impl n
   }"

definition f_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "f_time n = f1_time + f2_time (2 * n) + 1"
 
lemma f_rule [hoare_triple]:
  "<$(f_time (length xs))> 
    f_impl xs
   <\<lambda>r. fst r \<mapsto>\<^sub>a replicate (2*length xs) undefined *
        snd r \<mapsto>\<^sub>a replicate (2*length xs) undefined>\<^sub>t" by auto2

lemma f_time_bound [asym_bound]: "(\<lambda>n. f_time n) \<in> \<Theta>(\<lambda>n. n)"
  unfolding f_time_def by auto2

setup \<open>del_prfstep_thm @{thm f_time_def}\<close>

end
