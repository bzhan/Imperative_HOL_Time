theory IHT_Karatsuba
  imports "../Functional/Karatsuba" IHT_Arrays
begin

section \<open>Imperative version of shift_plus\<close>

fun coeffs_shift_plus_ind_impl :: "nat \<Rightarrow> 'a::{heap,comm_ring_1} \<Rightarrow> 'a array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "coeffs_shift_plus_ind_impl s m a b 0 = (return ())"
| "coeffs_shift_plus_ind_impl s m a b (Suc n) = do {
     coeffs_shift_plus_ind_impl s m a b n;
     va \<leftarrow> Array_Time.nth a n;
     vb \<leftarrow> Array_Time.nth b (s + n);
     Array_Time.upd (s + n) (m * va + vb) b;
     return ()
   }"

lemma coeffs_shift_plus_ind_impl_correct [hoare_triple]:
  "n \<le> length as \<Longrightarrow> s + length as \<le> length bs \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(4 * n + 1)>
   coeffs_shift_plus_ind_impl s m a b n
   <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a coeffs_shift_add_array s m as bs n>"
@proof @induct n @with
  @subgoal "n = Suc n"
    @have "s + Suc n \<le> length bs"
    @have "Suc (s + n) = s + Suc n"
  @endgoal @end
@qed

definition coeffs_shift_plus_impl :: "nat \<Rightarrow> 'a::{heap,comm_ring_1} \<Rightarrow> 'a array \<Rightarrow> 'a array \<Rightarrow> unit Heap" where
  "coeffs_shift_plus_impl s m a b = do {
     la \<leftarrow> Array_Time.len a;
     coeffs_shift_plus_ind_impl s m a b la
   }"

definition coeffs_shift_plus_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "coeffs_shift_plus_time n = 4 * n + 2"

lemma coeffs_shift_plus_impl_correct [hoare_triple]:
  "s + length as \<le> length bs \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(coeffs_shift_plus_time (length as))>
   coeffs_shift_plus_impl s m a b
   <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a coeffs_shift_plus s m as bs>" by auto2

lemma coeffs_shift_plus_time_mono [backward]:
  "n \<le> m \<Longrightarrow> coeffs_shift_plus_time n \<le> coeffs_shift_plus_time m" by auto2

lemma coeffs_shift_plus_time_bound [asym_bound]:
  "(\<lambda>n. coeffs_shift_plus_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: coeffs_shift_plus_time_def) auto2

definition coeffs_plus_impl :: "'a::{heap,comm_ring_1} array \<Rightarrow> 'a array \<Rightarrow> unit Heap" where
  "coeffs_plus_impl a b = coeffs_shift_plus_impl 0 1 a b"

lemma coeffs_plus_impl_correct [hoare_triple]:
  "length as \<le> length bs \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(coeffs_shift_plus_time (length as))>
   coeffs_plus_impl a b
   <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a (bs +\<^sub>l as)>\<^sub>t" by auto2
setup \<open>del_prfstep_thm @{thm coeffs_shift_plus_time_def}\<close>

definition coeffs_splus_impl :: "nat \<Rightarrow> 'a::{heap,comm_ring_1} array \<Rightarrow> 'a array \<Rightarrow> unit Heap" where
  "coeffs_splus_impl s a b = coeffs_shift_plus_impl s 1 a b"

lemma coeffs_splus_impl_correct [hoare_triple]:
  "s + length as \<le> length bs \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(coeffs_shift_plus_time (length as))>
   coeffs_splus_impl s a b
   <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a (bs +\<^sub>l coeffs_monom_mult s as)>\<^sub>t" by auto2

section \<open>Subtraction creating a new array\<close>

(* Subtracting a from b. Assuming b is at least as big as a. *)
definition coeffs_minus_impl :: "'a::{heap,comm_ring_1} array \<Rightarrow> 'a array \<Rightarrow> 'a array Heap" where
  "coeffs_minus_impl a b = do {
     c \<leftarrow> acopy a;
     coeffs_shift_plus_impl 0 (-1) b c;
     return c
   }"

definition coeffs_minus_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "coeffs_minus_time n = acopy_time n + coeffs_shift_plus_time n + 1"

lemma coeffs_minus_impl_correct [hoare_triple]:
  "length bs \<le> length as \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(coeffs_minus_time (length as))>
   coeffs_minus_impl a b
   <\<lambda>c. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a (as -\<^sub>l bs)>\<^sub>t"
@proof
  @have "coeffs_shift_plus_time (length as) \<ge>\<^sub>t coeffs_shift_plus_time (length bs)"
@qed
setup \<open>del_prfstep_thm @{thm coeffs_minus_time_def}\<close>

lemma coeffs_minus_time_bound [asym_bound]:
  "(\<lambda>n. coeffs_minus_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: coeffs_minus_time_def) auto2

section \<open>Imperative version of coeffs_prod_ind\<close>

fun coeffs_prod_ind_impl :: "'a::{heap,comm_ring_1} array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> 'a array Heap" where
  "coeffs_prod_ind_impl a b 0 = do {
     la \<leftarrow> Array_Time.len a;
     lb \<leftarrow> Array_Time.len b;
     c \<leftarrow> Array_Time.new (la + lb - 1) 0;
     return c
   }"
| "coeffs_prod_ind_impl a b (Suc n) = do {
     c \<leftarrow> coeffs_prod_ind_impl a b n;
     y \<leftarrow> Array_Time.nth a n;
     coeffs_shift_plus_impl n y b c;
     return c
   }"

fun coeffs_prod_ind_impl_time :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "coeffs_prod_ind_impl_time la lb 0 = 4 + (la + lb - 1)"
| "coeffs_prod_ind_impl_time la lb (Suc n) = coeffs_prod_ind_impl_time la lb n + coeffs_shift_plus_time lb + 2"
setup \<open>fold add_rewrite_rule @{thms coeffs_prod_ind_impl_time.simps}\<close>

lemma coeffs_prod_ind_impl_correct [hoare_triple]:
  "n \<le> length as \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(coeffs_prod_ind_impl_time (length as) (length bs) n)>
    coeffs_prod_ind_impl a b n
   <\<lambda>c. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a coeffs_prod_ind as bs n>"
@proof @induct n @with
  @subgoal "n = Suc n"
    @have "n + length bs \<le> length as + length bs - 1"
  @endgoal @end
@qed

definition coeffs_prod_impl :: "'a::{heap,comm_ring_1} array \<Rightarrow> 'a array \<Rightarrow> 'a array Heap" where
  "coeffs_prod_impl a b = do {
     la \<leftarrow> Array_Time.len a;
     coeffs_prod_ind_impl a b la
   }"

definition coeffs_prod_impl_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where [rewrite]:
  "coeffs_prod_impl_time la lb = coeffs_prod_ind_impl_time la lb la + 1"

lemma coeffs_prod_impl_correct [hoare_triple]:
  "<a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(coeffs_prod_impl_time (length as) (length bs))>
   coeffs_prod_impl a b
   <\<lambda>c. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a coeffs_prod as bs>" by auto2

setup \<open>del_prfstep_thm @{thm coeffs_prod_impl_time_def}\<close>

section \<open>Implementation of shifting\<close>

definition coeffs_monom_mult_impl :: "nat \<Rightarrow> 'a::{heap,comm_ring_1} array \<Rightarrow> 'a array Heap" where
  "coeffs_monom_mult_impl n a = do {
     xs \<leftarrow> Array_Time.freeze a;
     Array_Time.of_list (replicate n 0 @ xs)
   }"

definition coeffs_monom_mult_time :: "nat \<Rightarrow> nat" where [rewrite]:
  "coeffs_monom_mult_time n = 2 + 2*n"

lemma coeffs_monom_mult_impl_rule [hoare_triple]:
  "<a \<mapsto>\<^sub>a as * $(coeffs_monom_mult_time (n + length as))>
    coeffs_monom_mult_impl n a
   <\<lambda>r. a \<mapsto>\<^sub>a as * r \<mapsto>\<^sub>a coeffs_monom_mult n as>\<^sub>t"
@proof @unfold "coeffs_monom_mult n as"
  @have "n + length as \<ge>\<^sub>t length as"  
@qed

lemma coeffs_monom_mult_time_bound [asym_bound]:
  "(\<lambda>n. coeffs_monom_mult_time n) \<in> \<Theta>(\<lambda>n. n)"
  by (simp only: coeffs_monom_mult_time_def) auto2

setup \<open>del_prfstep_thm @{thm coeffs_monom_mult_time_def}\<close>

section \<open>Implementation of Karatsuba\<close>

partial_function (heap_time) karatsuba_main_impl ::
  "'a::{heap,comm_ring_1} array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> 'a array Heap" where
 "karatsuba_main_impl a b n =
  (if n \<le> karatsuba_lower_bound then
     coeffs_prod_impl a b
   else let n2 = n div 2 in
    do {
      (f0, f1) \<leftarrow> asplit a n2;
      (g0, g1) \<leftarrow> asplit b n2;
      p1 \<leftarrow> karatsuba_main_impl f1 g1 (n - n2);
      fd \<leftarrow> coeffs_minus_impl f1 f0;
      gd \<leftarrow> coeffs_minus_impl g1 g0;
      p2 \<leftarrow> karatsuba_main_impl fd gd (n - n2);
      p3 \<leftarrow> karatsuba_main_impl f0 g0 n2;
      r \<leftarrow> coeffs_monom_mult_impl (n2 + n2) p1;
      mr \<leftarrow> coeffs_minus_impl p1 p2;
      coeffs_plus_impl p3 mr;
      coeffs_splus_impl n2 mr r;
      coeffs_plus_impl p3 r;
      return r
    })"

function karatsuba_main_impl_time :: "nat \<Rightarrow> nat" where
  "n \<le> karatsuba_lower_bound \<Longrightarrow> karatsuba_main_impl_time n =
     coeffs_prod_impl_time n n"
| "n > karatsuba_lower_bound \<Longrightarrow> karatsuba_main_impl_time n =
     (asplit_time n * 2 +
      coeffs_minus_time (n - n div 2) * 2 +
      coeffs_monom_mult_time (n + n - 1) +
      coeffs_minus_time ((n - n div 2) + (n - n div 2) - 1) +
      coeffs_shift_plus_time ((n div 2) + (n div 2) - 1) * 2 +
      coeffs_shift_plus_time ((n - n div 2) + (n - n div 2) - 1) + 1 +
      (2 * karatsuba_main_impl_time (n - n div 2) +
       karatsuba_main_impl_time (n div 2)))"
  by force simp_all
  termination by (relation "Wellfounded.measure (\<lambda>n. n)") (auto simp: karatsuba_lower_bound_def)
setup \<open>fold add_rewrite_rule @{thms karatsuba_main_impl_time.simps}\<close>

lemma karatsuba_main_impl_time_pos: "0 < karatsuba_main_impl_time x"
  by (cases "x \<le> karatsuba_lower_bound") (simp_all add: coeffs_prod_impl_time_def)

definition karatsuba_main_impl_time' :: "nat \<Rightarrow> real" where
  "karatsuba_main_impl_time' n = real (karatsuba_main_impl_time n)"

lemma div2_ceil: "nat \<lceil>real n / 2\<rceil> = n - n div 2" by linarith
lemma div2_ceil': "nat \<lceil>real n / 2\<rceil> = (n + 1) div 2" by linarith
lemma div2_floor: "nat \<lfloor>real n / 2\<rfloor> = n div 2" by linarith

lemma powr_1: "real x powr 1 = real x" by simp

lemma "(\<lambda>n. karatsuba_main_impl_time n) \<in> \<Theta>(\<lambda>n. real n powr log 2 3)"
  unfolding karatsuba_main_impl_time'_def[symmetric]
  apply (master_theorem2 1 p': 1 recursion: karatsuba_main_impl_time.simps(2)
         rew: karatsuba_main_impl_time'_def div2_ceil[symmetric] div2_floor[symmetric])
  prefer 6 apply (rule bigthetaD1)
          apply (simp only: div2_ceil' div2_floor powr_1) apply auto2
  by (simp_all add: powr_divide karatsuba_main_impl_time'_def
        karatsuba_main_impl_time_pos karatsuba_lower_bound_def)

lemma karatsuba_main_impl_correct [hoare_triple]:
  "length as = n \<Longrightarrow> length bs = n \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * $(karatsuba_main_impl_time n)>
    karatsuba_main_impl a b n
   <\<lambda>r. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * r \<mapsto>\<^sub>a karatsuba_main_list as bs n>\<^sub>t"
@proof
  @fun_induct "karatsuba_main_list as bs n" arbitrary a b
  @unfold "karatsuba_main_list as bs n"
@qed

end
