(* Author: Simon Wimmer *)

theory Knapsack 
  imports Main
begin

consts w :: "nat \<Rightarrow> nat"
consts v :: "nat \<Rightarrow> nat"

section "Functional Algorithm and its correctness"

fun knapsack :: "nat\<times>nat \<Rightarrow> nat" where
  "knapsack (0, W) = 0" |
  "knapsack (Suc i, W) = (if W < w (Suc i)
    then knapsack (i, W)
    else max (knapsack (i, W)) (v (Suc i) + knapsack (i, W - w (Suc i))))"
 
text \<open>
  The correctness proof closely follows Kleinberg & Tardos: "Algorithm Design",
  chapter "Dynamic Programming"
\<close>

definition
  "OPT n W = Max {\<Sum> i \<in> S. v i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W}"

lemma OPT_0:
  "OPT 0 W = 0"
  unfolding OPT_def by simp

lemma Max_add_left:
  "(x :: nat) + Max S = Max (((+) x) ` S)" (is "?A = ?B") if "finite S" "S \<noteq> {}"
proof -
  have "?A \<le> ?B"
    using that by (force intro: Min.boundedI)
  moreover have "?B \<le> ?A"
    using that by (force intro: Min.boundedI)
  ultimately show ?thesis
    by simp
qed

lemma OPT_Suc:
  "OPT (Suc i) W = (
    if W < w (Suc i)
    then OPT i W
    else max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)
  )" (is "?lhs = ?rhs")
proof -
  have OPT_in: "OPT n W \<in> {\<Sum> i \<in> S. v i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W}" for n W
    unfolding OPT_def by - (rule Max_in; force)
  from OPT_in[of "Suc i" W] obtain S where S:
    "S \<subseteq> {1..Suc i}" "sum w S \<le> W" and [simp]: "OPT (Suc i) W = sum v S"
    by auto

  have "OPT i W \<le> OPT (Suc i) W"
    unfolding OPT_def by (force intro: Max_mono)
  moreover have "v (Suc i) + OPT i (W - w (Suc i)) \<le> OPT (Suc i) W" if "w (Suc i) \<le> W"
  proof -
    have *: "
      v (Suc i) + sum v S = sum v (S \<union> {Suc i}) \<and> (S \<union> {Suc i}) \<subseteq> {1..Suc i}
      \<and> sum w (S \<union> {Suc i}) \<le> W" if "S \<subseteq> {1..i}" "sum w S \<le> W - w (Suc i)" for S
      using that \<open>w (Suc i) \<le> W\<close>
      by (subst sum.insert_if | auto intro: finite_subset[OF _ finite_atLeastAtMost])+
    show ?thesis
      unfolding OPT_def
      by (subst Max_add_left;
          fastforce intro: Max_mono finite_subset[OF _ finite_atLeastAtMost] dest: *
         )
  qed
  ultimately have "?lhs \<ge> ?rhs"
    by auto

  from S have *: "sum v S \<le> OPT i W" if "Suc i \<notin> S"
    using that unfolding OPT_def by (auto simp: atLeastAtMostSuc_conv intro!: Max_ge)

  have "sum v S \<le> OPT i W" if "W < w (Suc i)"
  proof (rule *, rule ccontr, simp)
    assume "Suc i \<in> S"
    then have "sum w S \<ge> w (Suc i)"
      using S(1) by (subst sum.remove) (auto intro: finite_subset[OF _ finite_atLeastAtMost])
    with \<open>W < _\<close> \<open>_ \<le> W\<close> show False
      by simp
  qed
  moreover have
    "OPT (Suc i) W \<le> max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)" if "w (Suc i) \<le> W"
  proof (cases "Suc i \<in> S")
    case True
    then have [simp]:
      "sum v S = v (Suc i) + sum v (S - {Suc i})" "sum w S = w (Suc i) + sum w (S - {Suc i})"
      using S(1) by (auto intro: finite_subset[OF _ finite_atLeastAtMost] sum.remove)
    have "OPT i (W - w (Suc i)) \<ge> sum v (S - {Suc i})"
      unfolding OPT_def using S by (fastforce intro!: Max_ge)
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by (auto dest: *)
  qed
  ultimately have "?lhs \<le> ?rhs"
    by auto
  with \<open>?lhs \<ge> ?rhs\<close> show ?thesis
    by simp
qed

theorem knapsack_correct:
  "OPT n W = knapsack (n, W)"
  by (induction n arbitrary: W; auto simp: OPT_0 OPT_Suc)
 
end
