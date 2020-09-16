theory IHT_Binary_Search
  imports
    "../Functional/BinarySearch" 
    "../SepLogicTime/SLTC_Main"
    "../Asymptotics/Asymptotics_1D"
begin

partial_function (heap_time)  binarysearch :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a array \<Rightarrow> bool Heap" where
  "binarysearch l r x a = (
    if l \<ge> r then return False
    else if l + 1 \<ge> r then do {
      v \<leftarrow> Array_Time.nth a l;
      return (v = x) }
    else let m = avg l r in do {
      v \<leftarrow> Array_Time.nth a m;
      (if v = x then return True
       else if v < x then binarysearch (m + 1) r x a
       else binarysearch l m x a)
    })" (* apply pat_completeness by auto
termination by (relation "Wellfounded.measure (\<lambda>(l,r,a,f). r-l)") auto
*)
  print_theorems

function binarysearch_time :: "nat \<Rightarrow> nat" where
  "n < 2 \<Longrightarrow> binarysearch_time n = 2"
| "n \<ge> 2 \<Longrightarrow> binarysearch_time n = 2 + binarysearch_time (n div 2)"
by force simp_all
termination by (relation "Wellfounded.measure (\<lambda>n. n)") auto

definition binarysearch_time' :: "nat \<Rightarrow> real" where
  "binarysearch_time' n = real (binarysearch_time n)"

lemma div_2_to_rounding:
  "n - n div 2 = nat \<lceil>n / 2\<rceil>" "n div 2 = nat \<lfloor>n / 2\<rfloor>" by linarith+

lemma binarysearch_time'_Theta: "(\<lambda>n. binarysearch_time' n) \<in> \<Theta>(\<lambda>n. ln (real n))"
  apply (master_theorem2 2.3 recursion: binarysearch_time.simps(2) rew: binarysearch_time'_def div_2_to_rounding)
  prefer 2 apply auto2
  by (auto simp: binarysearch_time'_def)

setup \<open>fold add_rewrite_rule @{thms binarysearch_time.simps}\<close>

lemma binarysearch_mono [backward]:
  "m \<le> n \<Longrightarrow> binarysearch_time m \<le> binarysearch_time n" 
proof (induction n arbitrary: m rule: less_induct)
  case (less n)
  show ?case
  proof (cases "m<2")
    case True
    then show ?thesis apply (cases "n<2") by auto
  next
    case False
    then show ?thesis using less(2) by (auto intro: less(1))
  qed
qed

lemma avg_diff1 [resolve]: "(l::nat) \<le> r \<Longrightarrow> r - (avg l r + 1) \<le> (r - l) div 2" by simp
lemma avg_diff2 [resolve]: "(l::nat) \<le> r \<Longrightarrow> avg l r - l \<le> (r - l) div 2" by simp

lemma binarysearch_correct [hoare_triple]:
  "r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs * $(binarysearch_time (r - l))>
   binarysearch l r x a
   <\<lambda>res. a \<mapsto>\<^sub>a xs * \<up>(res \<longleftrightarrow> binarysearch_fun l r x xs)>\<^sub>t"
@proof @fun_induct "binarysearch_fun l r x xs"
  @unfold "binarysearch_fun l r x xs"
  @case "l \<ge> r" @case "l + 1 \<ge> r"
  @let "m = avg l r"
  @have "r - l \<ge> 2" @with
    @have "l + 2 = 2 + l" @have "r \<ge> 2 + l"  (* TODO: simplify *)
  @end
  @case "xs ! m < x" @with
    @have "binarysearch_time ((r - l) div 2) \<ge>\<^sub>t binarysearch_time (r - (m + 1))"
  @end
  @case "xs ! m > x" @with
    @have "binarysearch_time ((r - l) div 2) \<ge>\<^sub>t binarysearch_time (m - l)"
  @end
@qed

lemma binarysearch_correct' [hoare_triple]:
  "sorted xs \<Longrightarrow> r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs * $(binarysearch_time (r - l))>
   binarysearch l r x a
   <\<lambda>res. a \<mapsto>\<^sub>a xs * \<up>(res \<longleftrightarrow> (\<exists>i. l \<le> i \<and> i < r \<and> xs ! i = x))>\<^sub>t"
  by auto2

end
