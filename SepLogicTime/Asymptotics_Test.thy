theory Asymptotics_Test
  imports Asymptotics_Recurrences
begin

(* Some test functions *)

definition f :: "nat \<Rightarrow> nat" where "f x = 4 * x + 1"
lemma f_bound [asym_bound]: "f \<in> \<Theta>(\<lambda>n. real n)" unfolding f_def by auto2

definition flog :: "nat \<Rightarrow> nat" where "flog x = nat \<lceil>log 2 x\<rceil>"
lemma flog_bound [asym_bound]: "flog \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding flog_def using abcd_lnx[of 0 1 1 0] by auto

definition g :: "nat \<Rightarrow> nat" where "g x = 5"
lemma g_bound [asym_bound]: "g \<in> \<Theta>(\<lambda>n. 1)" unfolding g_def by auto2

fun f_prod :: "nat \<times> nat \<Rightarrow> nat" where
  "f_prod (n,m) = n * m"

lemma f_prod_asym [asym_bound]: "f_prod \<in> \<Theta>\<^sub>2(\<lambda>x. real (fst x * snd x))"
  apply (subst surjective_pairing) unfolding f_prod.simps by auto2

fun f_sum :: "nat \<times> nat \<Rightarrow> nat" where
  "f_sum (n,m) = n + m"

lemma f_sum_asym [asym_bound]: "f_sum \<in> \<Theta>\<^sub>2(\<lambda>x. real (fst x) + real (snd x))"
  apply (subst surjective_pairing) unfolding f_sum.simps by auto2

lemma "(\<lambda>x::nat. real 1) \<in> \<Theta>(\<lambda>n. 1::real)" by auto2

lemma "(\<lambda>x. real (f (5 * x))) \<in> \<Theta>(\<lambda>n. real n)" by auto2

lemma "(\<lambda>n. f (n + 1) + n * flog (2 * n) + 3 * n * flog (n div 3)) \<in> \<Theta>(\<lambda>n. n * ln n)" by auto2

(* Examples of f applied to constants *)
declare f_def [rewrite]
lemma "(\<lambda>x::nat. real (f 5)) \<in> \<Theta>(\<lambda>n. 1::real)" by auto2

(* how to incorporate 1D into 2D *)

lemma "(\<lambda>(n,m). f (5*m)) \<in> \<Theta>\<^sub>2(\<lambda>(n::nat,m). real m)" by auto2

lemma "(\<lambda>(n,m). f (5*n)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). real n)" by auto2

lemma "(\<lambda>x. real (fst x * snd x + 2)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (n * m))" by auto2

lemma "(\<lambda>x. real (fst x * fst x + 2)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). real (n^2))" by auto2

lemma "(\<lambda>x. real (fst x * fst x + snd x)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). real (n^2) + real m)" by auto2

lemma "(\<lambda>(n,m). f_prod (n+1,m+1) + 1) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real n * real m)" by auto2

lemma "(\<lambda>(n,m). f_sum (n+1,m+1)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real n + real m)" by auto2

lemma "(\<lambda>(n,m). f_prod (n+1,m+1) + f_sum (n+1,m+1) + 1) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real n * real m)" by auto2

lemma "(\<lambda>(n,m). f n + flog m + n * m + f_prod (n div 3,m+1)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real n * real m)" by auto2

lemma "(\<lambda>(n,m). 1 + f n + flog m + f_sum (n+1, m+1)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real n + real m)" by auto2

lemma "(\<lambda>(n,m). (1 + f n) * m * flog m) \<in> \<Theta>\<^sub>2(\<lambda>(n::nat,m). n * m * ln m)" by auto2

lemma "(\<lambda>(n,m). (1 + f n) * m * flog m) \<in> \<Theta>\<^sub>2(\<lambda>(n::nat,m::nat). n * m * ln m)" by auto2

lemma "(\<lambda>(n,m). (f m + f n) * m) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (m^2) + real n * real m)" by auto2

lemma "(\<lambda>(n,m). m * (f m + f n)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (m^2) + real n * real m)" by auto2

lemma "(\<lambda>(n,m). (f m + n) * (m + f n)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (m^2) + real n * real m + real (n^2))" by auto2

lemma "(\<lambda>x. real ((fst x * fst x + fst x) * snd x)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). real (n^2) * real m)" by auto2

lemma "(\<lambda>(n,m). real ((n * n + n) * m)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). real (n^2) * real m)" by auto2

lemma "(\<lambda>(n,m). real (f m + n)) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). real (m + n))" by auto2

lemma "(\<lambda>(n,m). f m * m + n) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). m^2 + n)" by auto2

lemma "(\<lambda>(n,m). f m * m + m * n + n * f n) \<in> \<Theta>\<^sub>2(\<lambda>(n,m::nat). m^2 + m * n + n^2)" by auto2

(* Examples of f or f_sum applied to constants *)
declare f_sum.simps [rewrite]

lemma "(\<lambda>x. real (f 1)) \<in> \<Theta>\<^sub>2(\<lambda>(n::nat,m::nat). 1)"
  apply (subst surjective_pairing) by auto2

lemma "(\<lambda>x. real (f_sum (5,3))) \<in> \<Theta>\<^sub>2(\<lambda>(n::nat,m::nat). 1)"
  apply (subst surjective_pairing) by auto2

ML_file "landau_util_test.ML"

hide_const f g flog f_prod f_sum

end
