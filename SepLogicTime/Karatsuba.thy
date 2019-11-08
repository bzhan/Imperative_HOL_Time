theory Karatsuba
  imports "Auto2_HOL.Auto2_Main" Berlekamp_Zassenhaus.Karatsuba_Multiplication
begin

section \<open>List version of polynomial operations\<close>

fun coeffs_smult :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "coeffs_smult m [] = []"
| "coeffs_smult m (x # xs) = m * x # coeffs_smult m xs"
setup \<open>fold add_rewrite_rule @{thms coeffs_smult.simps}\<close>

lemma coeffs_smult [rewrite]: "Poly (coeffs_smult m xs) = smult m (Poly xs)"
  by (induct xs, auto)

lemma coeffs_smult_length [rewrite_arg]:
  "length (coeffs_smult m xs) = length xs"
@proof @induct xs @qed

lemma coeffs_smult_nth [rewrite]:
  "i < length (coeffs_smult m xs) \<Longrightarrow> coeffs_smult m xs ! i = m * xs ! i"
@proof @induct xs arbitrary i @qed

lemma coeffs_smult_one [rewrite]:
  "coeffs_smult 1 xs = xs" by auto2

definition coeffs_plus :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "+\<^sub>l" 65) where
  "xs +\<^sub>l ys = list (\<lambda>i. nth_default 0 xs i + nth_default 0 ys i) (max (length xs) (length ys))"

lemma coeffs_plus_length [rewrite_arg]:
  "length ys \<le> length xs \<Longrightarrow> length (xs +\<^sub>l ys) = length xs"
@proof @unfold "xs +\<^sub>l ys" @qed

lemma coeffs_plus_length' [rewrite_arg]:
  "length xs \<le> length ys \<Longrightarrow> length (xs +\<^sub>l ys) = length ys"
@proof @unfold "xs +\<^sub>l ys" @qed

lemma coeffs_plus_Poly [rewrite]: "Poly (f1 +\<^sub>l f0) = Poly f1 + Poly f0" 
proof (rule poly_eqI, unfold poly_of_list_def coeff_add coeff_Poly)
  fix i
  show "nth_default 0 (f1 +\<^sub>l f0) i = nth_default 0 f1 i + nth_default 0 f0 i" 
    unfolding coeffs_plus_def
    by (simp add: list_length list_nth max_def nth_default_def)
qed

definition coeffs_minus :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "-\<^sub>l" 65) where
  "xs -\<^sub>l ys = list (\<lambda>i. nth_default 0 xs i - nth_default 0 ys i) (max (length xs) (length ys))"

lemma coeffs_minus_length [rewrite_arg]:
  "length ys \<le> length xs \<Longrightarrow> length (xs -\<^sub>l ys) = length xs"
@proof @unfold "xs -\<^sub>l ys" @qed

lemma coeffs_minus_Poly [rewrite]: "Poly (f1 -\<^sub>l f0) = Poly f1 - Poly f0" 
proof (rule poly_eqI, unfold poly_of_list_def coeff_diff coeff_Poly)
  fix i
  show "nth_default 0 (f1 -\<^sub>l f0) i = nth_default 0 f1 i - nth_default 0 f0 i" 
    unfolding coeffs_minus_def
    by (simp add: list_length list_nth max_def nth_default_def)
qed

lemma arith1 [rewrite_back]: "(a::'a::comm_ring_1) - b = a + (-1) * b" by simp
lemma mult0_right [rewrite]: "(m::('a::comm_ring_1)) * 0 = 0" by auto
setup \<open>add_rewrite_rule @{thm nth_default_def}\<close>

lemma coeffs_plus_neg_is_minus [rewrite_back]:
  "xs +\<^sub>l coeffs_smult (-1) ys = xs -\<^sub>l ys"
@proof
  @unfold "xs -\<^sub>l ys"
  @unfold "xs +\<^sub>l coeffs_smult (-1) ys"
  @have "length (xs -\<^sub>l ys) = length (xs +\<^sub>l coeffs_smult (-1) ys)"
  @have "\<forall>i<length (xs -\<^sub>l ys). (xs -\<^sub>l ys) ! i = (xs +\<^sub>l coeffs_smult (-1) ys) ! i" @with
    @let "x = nth_default 0 xs i"
    @let "y = nth_default 0 ys i"
    @have "(xs -\<^sub>l ys) ! i = x - y"
    @have "(xs +\<^sub>l coeffs_smult (-1) ys) ! i = x + (-1) * y"
  @end
@qed

definition coeffs_monom_mult :: "nat \<Rightarrow> 'a::comm_ring_1 list \<Rightarrow> 'a list" where
  "coeffs_monom_mult n xs = replicate n 0 @ xs"

lemma coeffs_mono_mult [rewrite]:
  "Poly (coeffs_monom_mult n xs) = monom_mult n (Poly xs)"
proof (cases "Poly xs = 0")
  case True
  then show ?thesis by (auto simp: coeffs_monom_mult_def monom_mult_def Poly_append)
next
  case False
  then have N: "coeffs (Poly xs) \<noteq> []" and
      N2: "xs \<noteq> []"
    by (auto simp add: coeffs_eq_iff)  
  have "monom_mult n (Poly xs) = Poly (coeffs (monom_mult n (Poly xs)))"
    by simp
  also have "\<dots> = Poly (let xs = coeffs (Poly xs) in
    if xs = [] then xs else replicate n 0 @ xs)" unfolding monom_mult_code by simp
  also have "\<dots> = Poly (replicate n 0 @ coeffs (Poly xs))"
    using N by presburger
  also have "\<dots> = poly_of_list (coeffs_monom_mult n xs)"
    unfolding coeffs_monom_mult_def using N2 apply auto
    by (metis Poly_append Poly_coeffs coeffs_Poly)
  finally show ?thesis by simp
qed

lemma length_coeffs_monom_mult [rewrite_arg]:
  "length (coeffs_monom_mult n as) = n + length as"
@proof @unfold "coeffs_monom_mult n as" @qed

lemma coeffs_monom_mult_0 [rewrite]: "coeffs_monom_mult 0 xs = xs"
@proof @unfold "coeffs_monom_mult 0 xs" @qed

section \<open>General addition function\<close>

definition coeffs_shift_plus :: "nat \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "coeffs_shift_plus s m xs ys = list (\<lambda>i.
     if i < s then ys ! i else if i \<ge> s + length xs then ys ! i
     else ys ! i + m * xs ! (i - s)) (length ys)"
setup \<open>register_wellform_data ("coeffs_shift_plus s m xs ys", ["s + length xs \<le> length ys"])\<close>

lemma coeffs_shift_plus_correct [rewrite]:
  "s + length xs \<le> length ys \<Longrightarrow>
   coeffs_shift_plus s m xs ys = ys +\<^sub>l coeffs_smult m (coeffs_monom_mult s xs)"
@proof
  @unfold "ys +\<^sub>l coeffs_smult m (coeffs_monom_mult s xs)"
  @unfold "coeffs_monom_mult s xs"
@qed

lemma smult_monom_mult' [rewrite]: "smult a (monom_mult n q) = monom a n * q"
  by (metis monom_mult_unfold(1) mult.right_neutral smult_monom_mult)

lemma coeffs_shift_plus_Poly [rewrite]:
  "s + length xs \<le> length ys \<Longrightarrow>
   Poly (coeffs_shift_plus s m xs ys) = Poly ys + monom m s * Poly xs" by auto2

lemma coeffs_shift_plus_1 [rewrite]:
  "s + length xs \<le> length ys \<Longrightarrow>
   coeffs_shift_plus s 1 xs ys = ys +\<^sub>l coeffs_monom_mult s xs" by auto2

lemma coeffs_shift_minus_1 [rewrite]:
  "0 + length xs \<le> length ys \<Longrightarrow>
   coeffs_shift_plus 0 (-1) xs ys = ys -\<^sub>l xs" by auto2

fun coeffs_shift_add_array :: "nat \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "coeffs_shift_add_array s m xs ys 0 = ys"
| "coeffs_shift_add_array s m xs ys (Suc n) =
   (let ys' = coeffs_shift_add_array s m xs ys n in
      list_update ys' (s + n) (m * xs ! n + ys' ! (s + n)))"
setup \<open>fold add_rewrite_rule @{thms coeffs_shift_add_array.simps}\<close>

lemma coeffs_shift_add_array_length [rewrite_arg]:
  "n \<le> length xs \<Longrightarrow> s + length xs \<le> length ys \<Longrightarrow>
   length (coeffs_shift_add_array s m xs ys n) = length ys"
@proof @induct n @qed

lemma coeffs_shift_add_array_ind [rewrite]:
  "n \<le> length xs \<Longrightarrow> s + length xs \<le> length ys \<Longrightarrow> i < length ys \<Longrightarrow>
   coeffs_shift_add_array s m xs ys n ! i = (if i < s + n then coeffs_shift_plus s m xs ys ! i else ys ! i)"
@proof @induct n @with
  @subgoal "n = 0" @case "i < s" @endgoal
  @subgoal "n = Suc n"
    @case "i < s + Suc n" @with
      @case "i < s + n" @case "i = s + n"
      @have "s + Suc n = Suc (s + n)"
    @end
  @endgoal @end
@qed

lemma coeffs_shift_add_array [rewrite]:
  "s + length xs \<le> length ys \<Longrightarrow>
   coeffs_shift_add_array s m xs ys (length xs) = coeffs_shift_plus s m xs ys" by auto2

section \<open>Naive multiplication procedure\<close>

setup \<open>add_rewrite_rule @{thm Poly_snoc}\<close>
setup \<open>add_rewrite_rule @{thm Poly.simps(1)}\<close>
setup \<open>add_rewrite_rule @{thm Poly_replicate_0}\<close>

lemma ring_norm1 [resolve]: "(a + b) * c = a * c + b * (c::'a::comm_ring_1 poly)"
  by (simp add: comm_semiring_class.distrib)

(* Compute product by adding terms in g one-by-one. *)
fun coeffs_prod_ind :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "coeffs_prod_ind xs ys 0 = replicate (length xs + length ys - 1) 0"
| "coeffs_prod_ind xs ys (Suc n) =
   (let zs = coeffs_prod_ind xs ys n in
      coeffs_shift_plus n (xs ! n) ys zs)"
setup \<open>fold add_rewrite_rule @{thms coeffs_prod_ind.simps}\<close>

lemma coeffs_prod_ind_length [rewrite_arg]:
  "length (coeffs_prod_ind xs ys n) = length xs + length ys - 1"
@proof @induct n @qed

lemma poly_mult_ind [rewrite]:
  "length (p::'a::comm_ring_1 list) + length q \<le> length ys \<Longrightarrow>
   Poly ys = Poly p * Poly q \<Longrightarrow>
   Poly (coeffs_shift_plus (length p) a q ys) = Poly (p @ [a]) * Poly q" by auto2

lemma coeffs_prod_correct_ind [rewrite]:
  "n \<le> length xs \<Longrightarrow>
   Poly (coeffs_prod_ind xs ys n) = Poly (take n xs) * Poly ys"
@proof @induct n @with
  @subgoal "n = Suc n"
    @have "n + length ys \<le> length xs + length ys - 1"
  @endgoal @end
@qed

definition coeffs_prod :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "coeffs_prod xs ys = coeffs_prod_ind xs ys (length xs)"

lemma coeffs_prod_correct [rewrite]:
  "Poly (coeffs_prod xs ys) = Poly xs * Poly ys" by auto2

section \<open>Functional version of karatsuba\<close>

fun karatsuba_main_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "karatsuba_main_list f g n = (
   if n \<le> karatsuba_lower_bound then
     coeffs_prod f g
   else let
     n2 = n div 2;
     f0 = take n2 f; f1 = drop n2 f;
     g0 = take n2 g; g1 = drop n2 g;
     p1 = karatsuba_main_list f1 g1 (n - n2);
     p2 = karatsuba_main_list (f1 -\<^sub>l f0) (g1 -\<^sub>l g0) (n - n2);
     p3 = karatsuba_main_list f0 g0 n2
   in
     coeffs_monom_mult (n2 + n2) p1 +\<^sub>l coeffs_monom_mult n2 (p1 -\<^sub>l p2 +\<^sub>l p3) +\<^sub>l p3)"
declare karatsuba_main_list.simps [simp del]

lemma Poly_split_at [rewrite]:
  "monom_mult n (Poly (drop n f)) + Poly (take n f) = Poly f"
  by (metis (no_types, lifting) Lists_Thms.length_take Poly_append Poly_coeffs add.commute
       append_take_drop_id coeffs_0_eq_Nil drop_eq_Nil le_less monom_mult_unfold mult_zero_left not_less)

setup \<open>add_backward_prfstep @{thm div_le_mono}\<close>

lemma karatsuba_lower_bound_div [rewrite]: "karatsuba_lower_bound div 2 = 3"
  by (simp add: karatsuba_lower_bound_def)

lemma n_div_2_compl [resolve]: "(n::nat) - n div 2 = (n + 1) div 2" by linarith

lemma karatsuba_basic [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> n div 2 \<ge> 1"
@proof @have "karatsuba_lower_bound div 2 = 3" @qed

lemma karatsuba_basic2 [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> n - n div 2 \<ge> 1"
@proof @have "n - n div 2 = (n + 1) div 2" @qed

lemma karatsuba_diff1 [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> n div 2 + n div 2 \<ge> 1" by auto2

lemma karatsuba_diff2 [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> n \<ge> n div 2" by auto

lemma karatsuba_diff2' [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> n > n div 2" by auto

lemma karatsuba_diff3 [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> (n - n div 2) + (n - n div 2) \<ge> 1" by auto2

lemma karatsuba_diff4 [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> n - n div 2 < n"
@proof @have "n div 2 \<ge> 1" @qed

lemma karatsuba_diff5 [resolve]:
  "n > karatsuba_lower_bound \<Longrightarrow> n div 2 \<le> n - n div 2" by auto

setup \<open>add_rewrite_rule @{thm karatsuba_main_step}\<close>

lemma karatsuba_main_list_length [rewrite_arg]:
  "length f = n \<Longrightarrow> length g = n \<Longrightarrow>
   length (karatsuba_main_list f g n) = n + n - 1"
@proof
  @strong_induct n arbitrary f g
  @case "n \<le> karatsuba_lower_bound" @with
    @unfold "karatsuba_main_list f g n"
  @end
  @let "n2 = n div 2"
  @let "f0 = take n2 f" "f1 = drop n2 f"
  @let "g0 = take n2 g" "g1 = drop n2 g"
  @let "p1 = karatsuba_main_list f1 g1 (n - n2)"
  @let "p2 = karatsuba_main_list (f1 -\<^sub>l f0) (g1 -\<^sub>l g0) (n - n2)"
  @let "p3 = karatsuba_main_list f0 g0 n2"
  @let "res = coeffs_monom_mult (n2 + n2) p1 +\<^sub>l coeffs_monom_mult n2 (p1 -\<^sub>l p2 +\<^sub>l p3) +\<^sub>l p3"
  @have "n2 \<le> n - n2"
  @apply_induct_hyp "n - n2" f1 g1
  @apply_induct_hyp "n - n2" "f1 -\<^sub>l f0" "g1 -\<^sub>l g0"
  @apply_induct_hyp n2 f0 g0
  @have "length (coeffs_monom_mult n2 (p1 -\<^sub>l p2 +\<^sub>l p3)) = n + (n - n2) - 1" @with
    @have "n2 + n2 - 1 \<le> (n - n2) + (n - n2) - 1"
  @end
  @have "length (coeffs_monom_mult (n2 + n2) p1) = n + n - 1"
  @have "length res = n + n - 1" @with
    @have "n2 + n2 - 1 \<le> (n - n2) + (n - n2) - 1"
    @have "(n - n2) + (n - n2) - 1 \<le> n + n - 1"
    @have "n + (n - n2) - 1 \<le> n + n - 1"
  @end
  @unfold "karatsuba_main_list f g n"
@qed

lemma karatsuba_main_list_correct:
  "Poly (karatsuba_main_list f g n) = Poly f * Poly g"
@proof
  @strong_induct n arbitrary f g
  @case "n \<le> karatsuba_lower_bound" @with
    @unfold "karatsuba_main_list f g n"
  @end
  @let "n2 = n div 2"
  @let "f0 = take n2 f" "f1 = drop n2 f"
  @let "g0 = take n2 g" "g1 = drop n2 g"
  @apply_induct_hyp "n - n2" f1 g1
  @apply_induct_hyp "n - n2" "f1 -\<^sub>l f0" "g1 -\<^sub>l g0"
  @apply_induct_hyp n2 f0 g0
  @let "p1 = karatsuba_main_list f1 g1 (n - n2)"
  @let "p2 = karatsuba_main_list (f1 -\<^sub>l f0) (g1 -\<^sub>l g0) (n - n2)"
  @let "p3 = karatsuba_main_list f0 g0 n2"
  @let "res = coeffs_monom_mult (n2 + n2) p1 +\<^sub>l coeffs_monom_mult n2 (p1 -\<^sub>l p2 +\<^sub>l p3) +\<^sub>l p3"
  @have "Poly res = monom_mult (n2 + n2) (Poly p1) + monom_mult n2 (Poly p1 - Poly p2 + Poly p3) + Poly p3"
  @have "Poly res = monom_mult (n2 + n2) (Poly p1) + (monom_mult n2 (Poly p1 - Poly p2 + Poly p3) + Poly p3)"
  @unfold "karatsuba_main_list f g n"
@qed

end
