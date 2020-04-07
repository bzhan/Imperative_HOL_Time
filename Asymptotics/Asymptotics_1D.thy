theory Asymptotics_1D
  imports Akra_Bazzi.Akra_Bazzi_Method Auto2_HOL.Auto2_Main
begin

section \<open>Eventually nonneg\<close>

lemma event_nonneg_real: "eventually_nonneg F (\<lambda>x. real (f x))"
  by (simp add: eventually_nonneg_def)

lemma event_nonneg_ln: "eventually_nonneg at_top (\<lambda>x. ln (real x))"
  unfolding eventually_nonneg_def apply(rule eventually_sequentiallyI[where c=1]) 
  using ln_ge_zero real_of_nat_ge_one_iff by blast 

lemma event_nonneg_ln_pow: "eventually_nonneg at_top (\<lambda>x. ln (real x) ^ m)"
  using event_nonneg_ln by (simp add: eventually_mono eventually_nonneg_def)

lemma event_nonneg_add':
  "eventually_nonneg F f \<Longrightarrow> eventually_nonneg F g \<Longrightarrow> eventually_nonneg F (f + g)"
  by (subst plus_fun_def) (rule eventually_nonneg_add)

lemma event_nonneg_mult':
  "eventually_nonneg F f \<Longrightarrow> eventually_nonneg F g \<Longrightarrow> eventually_nonneg F (f * g)"
  apply (subst times_fun_def) by (rule eventually_nonneg_mult)

section \<open>Normal form in one variale\<close>

definition polylog :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "polylog a b x = real (x^a) * (ln x)^b"

lemma event_nonneg_polylog: "eventually_nonneg at_top (\<lambda>x. polylog a b x)"
  apply (simp only: polylog_def)
  apply (rule eventually_nonneg_mult)
   apply (rule event_nonneg_real)
   apply (rule event_nonneg_ln_pow)
  done

lemma poly_log_compare:
  "(a1<a2 \<or> (a1=a2 \<and> b1<b2)) \<Longrightarrow> (\<lambda>x. polylog a1 b1 x) \<in> o(\<lambda>x. polylog a2 b2 x)"
  unfolding polylog_def by auto

section \<open>Stability in one variable\<close>

definition stablebigO :: "(nat \<Rightarrow> real) \<Rightarrow> bool" where (* 'a::real_normed_field *)
  "stablebigO f = (\<forall>c>0. (\<lambda>x. f (c * x)) \<in> O(f))"  

lemma stablebiOI: assumes "\<And>c. 0 < c \<Longrightarrow> (\<lambda>x. f (c * x)) \<in> O(f)"
  shows "stablebigO f"
  unfolding stablebigO_def using assms by blast

lemma stablebigOD: assumes "stablebigO f" "d>0" 
  obtains c where "c>0" "eventually (\<lambda>x.  norm (f (d*x)) \<le> c *  norm (f x)) at_top"
proof -
  from assms have "(\<lambda>x. f (d * x)) \<in> O(f)" unfolding stablebigO_def by auto
  then obtain c where "c>0" "eventually (\<lambda>x. norm (f (d * x)) \<le> c * norm (f x)) at_top" 
    using landau_o.bigE by blast
  then show ?thesis by (rule that)
qed
                               
lemma stablebigO_linear: "stablebigO (\<lambda>n::nat. n)"
  unfolding stablebigO_def by auto

lemma stablebigO_poly: "stablebigO (\<lambda>n::nat. n^m)"
  unfolding stablebigO_def by auto

lemma stablebigO_ln: "stablebigO (\<lambda>x. ln (real x))"
  unfolding stablebigO_def by auto

lemma stablebigO_lnpower: "stablebigO (\<lambda>x. (ln (real x))^m)"
  unfolding stablebigO_def by auto

lemma stablebigO_mult:
  fixes f g :: "nat \<Rightarrow> real"
  assumes f: "stablebigO f" and g: "stablebigO g" and
     evf: "eventually_nonneg at_top f" and
     evg: "eventually_nonneg at_top g"
  shows "stablebigO (f * g)"
proof (rule stablebiOI)
  fix d :: nat
  assume d: "d>0"
  from f d obtain cf where cf: "cf>0" and f: "eventually (\<lambda>x. norm (f (d * x)) \<le> cf * norm (f x)) at_top" 
    using stablebigOD by blast
  from g d obtain cg where cg: "cg>0" and g: "eventually (\<lambda>x. norm (g (d * x)) \<le> cg * norm (g x)) at_top" 
    using stablebigOD by blast
                                                                               
  have evf: "eventually (\<lambda>x. f x \<ge> 0) at_top" using evf by (simp add: eventually_nonneg_def)
  have evg: "eventually (\<lambda>x. g x \<ge> 0) at_top" using evg by (simp add: eventually_nonneg_def)
      
  let ?c = "cf * cg"
  note prem = f evf[unfolded eventually_nonneg_def] g evg[unfolded eventually_nonneg_def]  

  show "(\<lambda>x. (f * g) (d * x)) \<in> O(f * g)"
    apply(rule bigoI[where c="?c"])
    using prem
  proof eventually_elim
    case (elim x)
    have "norm ((f*g)(d*x)) = norm(f (d*x)*g (d*x))" by auto
    also have "\<dots> =  norm(f (d*x)) * norm (g (d*x))"
      by (metis norm_mult)         
    also have "\<dots> \<le> (cf * norm (f x)) * norm (g (d*x))" using elim(1) by (auto intro!: mult_right_mono)
    also have "\<dots> \<le> (cf * norm (f x)) * (cg * norm (g x))" using cf elim(2,3) by (auto intro!: mult_left_mono)
    also have "\<dots> = ?c * (norm (f x * g x))" using cg cf
      by (metis mult.commute mult.left_commute norm_mult) 
    finally show ?case by auto
  qed                
qed 

lemma stablebigO_mult':
  fixes f g :: "nat \<Rightarrow> real"
  assumes "stablebigO f" "stablebigO g" 
     "eventually_nonneg at_top f" "eventually_nonneg at_top g"
   shows "stablebigO (%x. f x * g x)"
proof -
  have "(\<lambda>x. f x * g x)  = f * g" by auto
  with stablebigO_mult[OF assms] show ?thesis by simp
qed

lemma stable_polylog: "stablebigO (\<lambda>x. polylog a b x)"
  apply (simp only: polylog_def)
  apply (rule stablebigO_mult')
   apply (rule stablebigO_poly)
   apply (rule stablebigO_lnpower)
   apply (rule event_nonneg_real)
   apply (rule event_nonneg_ln_pow)
  done


lemma stablebigO_plus:
  fixes f g :: "nat \<Rightarrow> real"
  assumes f: "stablebigO f" and g: "stablebigO g" and
     evf: "eventually_nonneg at_top f" and
     evg: "eventually_nonneg at_top g"
  shows "stablebigO (f + g)"
proof (rule stablebiOI)
  fix d :: nat
  assume d: "d>0"
  from f d obtain cf where f: "eventually (\<lambda>x. norm (f (d * x)) \<le> cf * norm (f x)) at_top" 
    using stablebigOD by blast
  from g d obtain cg where g: "eventually (\<lambda>x. norm (g (d * x)) \<le> cg * norm (g x)) at_top" 
    using stablebigOD by blast

  have evf: "eventually (\<lambda>x. f x \<ge> 0) at_top" using evf by (simp add: eventually_nonneg_def)
  have evg: "eventually (\<lambda>x. g x \<ge> 0) at_top" using evg by (simp add: eventually_nonneg_def)
  
  let ?c = "(max cf cg)"
  note prem = f evf[unfolded eventually_nonneg_def] g evg[unfolded eventually_nonneg_def]  

  show "(\<lambda>x. (f + g) (d * x)) \<in> O(f + g)"
    apply(rule bigoI[where c="?c"])
    using prem
  proof eventually_elim
    case (elim x) 
    have "norm ((f+g)(d*x)) = norm(f (d*x)+g (d*x))" by auto
    also have "\<dots> \<le>  norm(f (d*x)) + norm (g (d*x))" by (simp add: norm_triangle_ineq) 
    also have "\<dots> \<le> cf * norm (f x) + cg * norm (g x)" using elim(1,3) by auto
    also have "\<dots> \<le> ?c * norm (f x) + ?c * norm (g x)" by (simp add: max_def mult_right_mono)
    also have "\<dots> = ?c * (norm (f x)+ norm (g x))" by (simp add: distrib_left) 
    also have "\<dots> = ?c * norm (f x + g x)" using elim(2,4) by auto
    finally show ?case by auto                 
  qed
qed

section \<open>Eventual monotonicity in one variable\<close>

definition event_mono :: "(nat \<Rightarrow> real) \<Rightarrow> bool" where
  "event_mono g1 = eventually (\<lambda>x1. \<forall>x2\<ge>x1. norm (g1 x1) \<le> norm (g1 x2)) at_top"

lemma event_mono_linear: "event_mono (\<lambda>n::nat. n)"
  unfolding event_mono_def by auto

lemma event_mono_poly: "event_mono (\<lambda>n::nat. n^m)"
  unfolding event_mono_def apply (auto simp: eventually_sequentially)
  apply(rule exI[where x=1]) apply auto apply(rule power_mono) by auto

lemma event_mono_ln: "event_mono (\<lambda>x. ln (real x))"
  unfolding event_mono_def apply (auto simp: eventually_sequentially)
  apply(rule exI[where x=1]) by auto

lemma event_mono_lnpower: "event_mono (\<lambda>x. (ln (real x))^m)"
  unfolding event_mono_def apply (auto simp: eventually_sequentially)
  apply(rule exI[where x=1]) apply(auto) apply(rule power_mono) by auto

lemma assumes f : "event_mono f" and g: "event_mono g" and
     evf: "eventually_nonneg at_top f" and
     evg: "eventually_nonneg at_top g"
  shows event_mono_plus: "event_mono (\<lambda>x. f x + g x)" 
proof -
  from evf have evf': "eventually (\<lambda>x. \<forall>x'\<ge>x. f x' \<ge> 0) at_top"
    using eventually_all_ge_at_top eventually_nonneg_def by blast
  from evg have evg': "eventually (\<lambda>x. \<forall>x'\<ge>x. g x' \<ge> 0) at_top"
    using eventually_all_ge_at_top eventually_nonneg_def by blast
 
  note prem = evf' f[unfolded event_mono_def] g[unfolded event_mono_def] evg'

  show ?thesis
    unfolding event_mono_def
    using prem
  proof eventually_elim
    case (elim x1)
    show "\<forall>x2\<ge>x1. norm (f x1 + g x1) \<le> norm (f x2 + g x2)"
    proof safe
      fix x2 assume x2: "x2\<ge>x1" 
      with elim have e: "f x2 \<ge> 0" "g x2 \<ge> 0" by auto
      have "norm (f x1 + g x1) \<le> norm (f x1) + norm (g x1)" by (simp add: norm_triangle_ineq) 
      also have "\<dots> \<le> norm (f x2) + norm (g x2)" using elim(2,3) x2 by force
      also have "\<dots> = norm (f x2 + g x2)" using e by simp
      finally show "norm (f x1 + g x1) \<le> norm (f x2 + g x2)" .
    qed
  qed    
qed

lemma assumes f : "event_mono f" and g: "event_mono g"
  shows event_mono_mult: "event_mono (\<lambda>x. f x * g x)" 
proof - 
  note B=eventually_conj[OF f[unfolded event_mono_def] g[unfolded event_mono_def]]
  show ?thesis unfolding event_mono_def
  proof(rule eventually_mono[OF B], safe, simp )
    fix x1 x2
    assume a: "\<forall>x2\<ge>x1. \<bar>f x1\<bar> \<le> \<bar>f x2\<bar>"
    assume b: "\<forall>x2\<ge>x1. \<bar>g x1\<bar> \<le> \<bar>g x2\<bar>"
    assume c: "x1 \<le> x2"
    have "\<bar>f x1 * g x1\<bar> = \<bar>f x1\<bar> * \<bar>g x1\<bar>"  by (metis abs_mult)          
    also have       "\<dots> \<le> \<bar>f x2\<bar> * \<bar>g x1\<bar>" using a c by (auto intro: mult_right_mono)
    also have       "\<dots> \<le> \<bar>f x2\<bar> * \<bar>g x2\<bar>" using b c by (auto intro: mult_left_mono)  
    also have       "\<dots> = \<bar>f x2 * g x2\<bar>" by (metis abs_mult)  
    finally show "\<bar>f x1 * g x1\<bar> \<le> \<bar>f x2 * g x2\<bar>" .
  qed
qed

lemma event_mono_polylog: "event_mono (\<lambda>x. polylog a b x)"
  apply (simp only: polylog_def)
  apply (rule event_mono_mult)
   apply (rule event_mono_poly)
   apply (rule event_mono_lnpower)
  done


section \<open>Auxiliary basics about Landau symbols\<close>

lemma bigomegaI [intro]:
  assumes "\<forall>\<^sub>F x in F. norm (g x) \<le> c * (norm (f x))"
  shows   "f \<in> \<Omega>[F](g)"
proof (rule landau_omega.bigI)
  show "1 / max 1 c > 0" by simp
  note assms  
  have *: "\<And>x. c * norm (f x) \<le> max 1 c * norm (f x)"   by (simp add: mult_right_mono) 
  show "\<forall>\<^sub>F x in F. (1 / max 1 c) * norm (g x) \<le> norm (f x)"
    apply(rule eventually_mono)
     apply(fact)
    using *
    by (metis \<open>0 < 1 / max 1 c\<close> mult.commute mult.left_neutral order_trans pos_divide_le_eq times_divide_eq_right zero_less_divide_1_iff)  
qed

lemma bigOmegaE:
  fixes f :: "nat \<Rightarrow> real"
  assumes "f \<in> \<Omega>(g)"
  obtains c n where "c > 0" "\<forall>x\<ge>n. norm (f x) \<ge> c * norm (g x)"
proof -
  from assms obtain c where c1: "c>0" and
      "\<forall>\<^sub>F x in at_top. norm (f x) \<ge> c * norm (g x)" using landau_omega.bigE by blast
  then obtain n where f1: "\<forall>x\<ge>n. norm (f x) \<ge> c * norm (g x)" 
    by (meson eventually_at_top_linorder)   
  from c1 and f1 show ?thesis by (rule that)
qed 

lemma bigOE: 
  fixes f :: "nat\<Rightarrow>real"
  assumes "f \<in> O(g)"
  obtains c n where "c > 0" "\<forall>x\<ge>n. norm (f x) \<le> c * norm (g x)"
proof -
  from assms obtain c where c1: "c>0" and
      "\<forall>\<^sub>F x in at_top. norm (f x) \<le> c * norm (g x)" using landau_o.bigE by blast
  then obtain n where f1: "\<forall>x\<ge>n. norm (f x) \<le> c * norm (g x)" 
    by (meson eventually_at_top_linorder)   
  from c1 and f1 show ?thesis by (rule that)
qed 

lemma bigOE_nat:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "f \<in> O(g)"
  obtains c n :: nat where "c > 0" "\<forall>x\<ge>n. f x \<le> c * g x"
proof -
  from assms obtain c where c1: "c>0" and
      "\<forall>\<^sub>F x in at_top. norm (f x) \<le> c * norm (g x)" using landau_o.bigE by blast
  then obtain n where f1: "\<forall>x\<ge>n. norm (f x) \<le> c * norm (g x)" 
    by (meson eventually_at_top_linorder)  
  have c1': "(nat \<lceil>c\<rceil>) > 0" using c1 by auto
  {fix x assume "x\<ge>n"
    with f1 have f1': "f x \<le> c * g x" by auto
    then have "f x \<le> (nat \<lceil>c\<rceil>) * g x" using c1
      by (smt mult_right_mono of_nat_0_le_iff of_nat_ceiling of_nat_le_iff of_nat_mult) 
  } then have "\<forall>x\<ge>n. f x \<le> (nat \<lceil>c\<rceil>) * g x" by auto
  from c1' and this show ?thesis by (rule that)
qed

lemma bigOmegaE_nat:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "f \<in> \<Omega>(g)"
  obtains c n :: nat where "c>0" "\<forall>x\<ge>n. g x \<le> c * f x"
proof -
  from assms obtain c where c1: "c>0" and
      "\<forall>\<^sub>F x in at_top. norm (f x) \<ge> c * norm (g x)" using landau_omega.bigE by blast
  then obtain n where f1: "\<forall>x\<ge>n. norm (f x) \<ge> c * norm (g x)" 
    by (meson eventually_at_top_linorder)   
  from c1 have ic: "1/c \<le> (nat \<lceil>1/c\<rceil>)" by linarith
  have 1: "(nat \<lceil>1/c\<rceil>) > 0 "using c1
    by simp 
  {fix x assume "x\<ge>n"
    with f1 have f1': "f x \<ge> c * g x" by auto
    with c1 have "g x \<le> f x / c"
      by (simp add: mult.commute mult_imp_le_div_pos) 
    also have "\<dots> \<le> (nat \<lceil>1/c\<rceil>) * f x" using ic
      using mult_right_mono by fastforce  
    finally have "real (g x) \<le> real ((nat \<lceil>1/c\<rceil>) * f x)" .
    then have "g x \<le> (nat \<lceil>1/c\<rceil>) * f x"
      by linarith  
  } then have "\<forall>x\<ge>n. g x \<le> (nat \<lceil>1/c\<rceil>) * f x" by auto
  from 1 and this show ?thesis by (rule that)
qed 

lemma fsmall': "\<And>(f::nat\<Rightarrow>real) c::real. f \<in> \<omega>(\<lambda>n::real. 1::real) \<Longrightarrow> c\<ge>0 \<Longrightarrow> (\<exists>n. \<forall>x\<ge>n. c \<le> norm (f x))"
proof -
  fix f::"nat\<Rightarrow>real" and c :: real
  assume c: "c\<ge>0" and  w: " f \<in> \<omega>(\<lambda>n::real. 1::real)"  
  then have "c+1 > 0" by auto
  from landau_omega.smallD[OF w this]
    have "\<forall>\<^sub>F x in at_top. norm (f x) \<ge> (c+1) * norm (1::real)"  by auto
  then obtain N where "\<And>x. x\<ge>N \<Longrightarrow> norm (f x) \<ge> c+1 "
    unfolding eventually_at_top_linorder by fastforce
  then have "\<And>x. x\<ge>N \<Longrightarrow> norm (f x) \<ge> c" by force
  then show "\<exists>n. \<forall>x\<ge>n. c \<le> norm (f x)" by auto
qed
 

lemma fsmall_ev: "\<And>(f::nat\<Rightarrow>nat) (c::nat). f \<in> \<omega>(\<lambda>n::real. 1::real) \<Longrightarrow> 
      eventually (\<lambda>x. c \<le> f x) at_top"
proof -
  fix f::"nat\<Rightarrow>nat" and c :: nat
  assume w: " f \<in> \<omega>(\<lambda>n::real. 1::real)"  
  then have "real (c+1) > 0" by auto
  from landau_omega.smallD[OF w this]
   have "\<forall>\<^sub>F x in at_top. norm (f x) \<ge> (real (c+1)) * norm (1::real)"  by auto
  then obtain N where "\<And>x. x\<ge>N \<Longrightarrow>  f x \<ge> c+1 "
    unfolding eventually_at_top_linorder by fastforce
  then have "\<And>x. x\<ge>N \<Longrightarrow>  f x \<ge> c" by force
  then have "\<exists>n. \<forall>x\<ge>n. c \<le> f x" by auto
  then show "eventually (\<lambda>x. c \<le> f x) at_top" unfolding eventually_sequentially
    by blast
qed

lemma fsmall: "\<And>(f::nat\<Rightarrow>nat) (c::nat). f \<in> \<omega>(\<lambda>n::real. 1::real) \<Longrightarrow> (\<exists>n. \<forall>x\<ge>n. c \<le> f x)"
proof -
  fix f::"nat\<Rightarrow>nat" and c :: nat
  assume w: " f \<in> \<omega>(\<lambda>n::real. 1::real)"  
  then have "real (c+1) > 0" by auto
  from landau_omega.smallD[OF w this]
   have "\<forall>\<^sub>F x in at_top. norm (f x) \<ge> (real (c+1)) * norm (1::real)"  by auto
  then obtain N where "\<And>x. x\<ge>N \<Longrightarrow>  f x \<ge> c+1 "
    unfolding eventually_at_top_linorder by fastforce
  then have "\<And>x. x\<ge>N \<Longrightarrow>  f x \<ge> c" by force
  then show "\<exists>n. \<forall>x\<ge>n. c \<le> f x" by auto
qed

lemma fbig: "\<And>(f::nat\<Rightarrow>nat) (c::nat). f \<in> \<Omega>(\<lambda>n. n) \<Longrightarrow> (\<exists>n. \<forall>x\<ge>n. c \<le> f x)"
proof -
  fix f::"nat\<Rightarrow>nat" and c :: nat
  assume " f \<in> \<Omega>(\<lambda>n. n)" 
  then obtain c1 where c1: "c1>0" and
    "\<forall>\<^sub>F x in at_top. norm (f x) \<ge> c1 * norm (x)" using landau_omega.bigE by blast
  then obtain n where f: "\<forall>x\<ge>n. norm (f x) \<ge> c1 * norm (x)" 
    by (meson eventually_at_top_linorder)  
  { fix x :: nat
    assume "x\<ge>max (nat \<lceil>c/c1\<rceil>) n"
    then have xn: "x\<ge>n" and xc: "real x\<ge>(real c/c1)" by auto
    from xc have "real c \<le> c1 * x" using c1
      by (metis nonzero_mult_div_cancel_left not_le order_refl real_mult_le_cancel_iff2 times_divide_eq_right)
    also have "c1 * x \<le> f x" using f xn by auto
    finally have "c \<le> f x" by auto
  }
  then have "\<forall>x\<ge>max (nat \<lceil>c/c1\<rceil>) n. c \<le> f x" by auto
  then show "\<exists>n. \<forall>x\<ge>n. c \<le> f x" by blast
qed


section \<open>Composition in 1 variable case\<close>

lemma bigOmega_compose:
  fixes f1  g1 :: "nat\<Rightarrow>real" and f2 g2:: "nat \<Rightarrow> nat"
  assumes "stablebigO g1"
    and "f1 \<in> \<Omega>(g1)" "f2 \<in> \<Omega>(g2)"
    and "f2 \<in> \<omega>(\<lambda>n. 1)" "g2 \<in> \<omega>(\<lambda>n. 1)"
    and monog1: "event_mono g1"
  shows "f1 o f2 \<in> \<Omega>(g1 o g2)"
proof -
  from assms(2) obtain c1 and n1 :: nat where c1: "c1>0" and
      "\<And>x. x \<ge> n1 \<Longrightarrow>  c1 * norm (g1 x) \<le>norm (f1 x)" using bigOmegaE by blast
  then have f1: "\<And>x. x \<ge> n1 \<Longrightarrow>   norm (g1 x) \<le>norm (f1 x) / c1" using c1
    by (simp add: le_divide_eq mult.commute pos_le_divide_eq)                                                

  from assms(3) obtain c2 n2 :: nat where  c2: "c2>0"   and
    f2: "\<And>x. x \<ge> n2 \<Longrightarrow> g2 x \<le> c2 * f2 x" using bigOmegaE_nat by blast

  from assms(1)[unfolded stablebigO_def] c2 
    obtain c3 :: real and n3 :: nat where c3: "c3>0" and
    f3: "\<And>x. x\<ge>n3 \<Longrightarrow> norm (g1 (c2 * x)) \<le> c3 * norm (g1 x)" using bigOE by blast

  from monog1[unfolded event_mono_def] obtain nM
    where g1: "\<And>x y. x \<ge> nM \<Longrightarrow> y\<ge>x \<Longrightarrow>  norm (g1 x) \<le> norm (g1 y)"
    unfolding eventually_sequentially by blast 

  from assms(4) fsmall_ev have 1: "\<forall>\<^sub>F x in sequentially. n1 \<le> f2 x" by force
  from assms(4) fsmall_ev have 2: "\<forall>\<^sub>F x in sequentially. n3 \<le> f2 x" by force
  from assms(5) fsmall_ev have 3: "\<forall>\<^sub>F x in sequentially. nM \<le> g2 x" by force
  have "\<forall>\<^sub>F x in sequentially. n2 \<le> x" by simp

  from 1 2 3 this have "\<forall>\<^sub>F x in sequentially. norm ((g1 \<circ> g2) x) \<le> c3 / c1 * norm ((f1 \<circ> f2) x)"
  proof eventually_elim
    case (elim x)
    with g1 have g1: "\<And>y. y\<ge>g2 x \<Longrightarrow>  norm (g1 (g2 x)) \<le> norm (g1 y)" by auto

    have "g2 x \<le> c2 * f2 x" using f2 elim by auto
    then have "norm (g1 (g2 x)) \<le> norm(g1 (c2 * f2 x))" by(rule g1)
    also have "\<dots> \<le> c3 * norm (g1 (f2 x))" using f3 elim by simp
    also have "\<dots> \<le> c3 * (norm (f1 (f2 x))/c1)" apply(rule mult_left_mono) using c3 f1 elim by auto 
    also have "\<dots> = (c3/c1) * norm (f1 (f2 x))" by auto
    finally show ?case by auto
  qed 
  thus ?thesis by(rule bigomegaI[where c="c3/c1"])
qed 

lemma bigO_compose:
  fixes f1  g1 :: "nat \<Rightarrow> real" and f2 g2:: "nat \<Rightarrow> nat"
  assumes "stablebigO g1"
    and "f1 \<in> O(g1)"  and 2: "f2 \<in> O(g2)"
    and "f2 \<in> \<omega>(\<lambda>n. 1)" and "g2 \<in> \<omega>(\<lambda>n. 1)"
    and monog1: "event_mono g1"
  shows "f1 o f2 \<in> O(g1 o g2)"
proof -
  from assms(2) obtain c1 :: real and n1 :: nat where c1: "c1>0" and
    f1: "\<And>x. x\<ge>n1 \<Longrightarrow> norm (f1 x) \<le> c1 * norm (g1 x)" using bigOE  by blast 

  from 2 obtain c2 n2 :: nat where c2: "c2>0" and
    f2: "\<And>x. x\<ge>n2 \<Longrightarrow> f2 x \<le> c2 * g2 x" using bigOE_nat by blast 

  from assms(1)[unfolded stablebigO_def] c2
    obtain c3 ::real and n3 :: nat where c3: "c3>0" and
    f3: "\<And>x. x\<ge>n3 \<Longrightarrow> norm (g1 (c2 * x)) \<le> c3 * norm (g1 x)" using bigOE by blast

  from monog1[unfolded event_mono_def] obtain nM
    where g1: "\<And>x y. x \<ge> nM \<Longrightarrow> y\<ge>x \<Longrightarrow>  norm (g1 x) \<le> norm (g1 y)"
    unfolding  eventually_sequentially by blast 

  from assms(4) fsmall_ev have 1: "\<forall>\<^sub>F x in sequentially. n1 \<le> f2 x" by fast
  from assms(5) fsmall_ev have 2: "\<forall>\<^sub>F x in sequentially. n3 \<le> g2 x" by fast
  from assms(4) fsmall_ev have 3: "\<forall>\<^sub>F x in sequentially. nM \<le> f2 x" by fast
  have "\<forall>\<^sub>F x in sequentially. n2 \<le> x" by simp 
 
  from 1 2 3 this have "\<forall>\<^sub>F x in sequentially. norm ((f1 \<circ> f2) x) \<le> c1 * c3 * norm ((g1 \<circ> g2) x)"
  proof eventually_elim
    case (elim x) 
    have "norm (f1 (f2 x)) \<le> c1 * norm (g1 (f2 x))" using f1[where x="f2 x"] elim
      by blast 
    also { have "norm (g1 (f2 x)) \<le> norm (g1 (c2 * g2 x))"
        apply(rule g1) using f2 elim by auto 
      also have "\<dots> \<le> c3 * norm (g1 (g2 x))" using elim f3 by auto 
      finally have " c1 * norm (g1 (f2 x)) \<le> c1 * (c3 *  norm (g1 (g2 x)))"
        using c1 by auto  }    
    finally have "norm ((f1 \<circ> f2) x) \<le> (c1 * c3) * (norm (g1 (g2 x)))" by auto
    then show "norm (((f1 \<circ> f2) x)) \<le> (c1 * c3) * norm ((g1 \<circ> g2) x) "
      using of_nat_mono by fastforce 
  qed
  thus ?thesis by(rule bigoI[where c="c1 * c3"]) 
qed
 
lemma bigTheta_compose:
  fixes f1  g1 :: "nat\<Rightarrow>real" and f2 g2:: "nat \<Rightarrow> nat"
  assumes "stablebigO g1"
    and "f1 \<in> \<Theta>(g1)" "f2 \<in> \<Theta>(g2)"
    and "f2 \<in> \<omega>(\<lambda>n. 1)"
    and "event_mono g1"
  shows "f1 o f2 \<in> \<Theta>(g1 o g2)"
proof - 
  from assms(3,4) have z:  "g2 \<in> \<omega>(\<lambda>n. 1)"
    using landau_omega.small.in_cong_bigtheta by blast
  have "f1 o f2 \<in> O(g1 o g2)" apply(rule bigO_compose) using z assms by auto
  moreover have "f1 o f2 \<in> \<Omega>(g1 o g2)" apply(rule bigOmega_compose) using assms z by auto
  ultimately show ?thesis by auto
qed

lemma polylog_power_compose:
  "polylog a b o (\<lambda>n. n ^ c) \<in> \<Theta>(polylog (c * a) b)"
  unfolding polylog_def unfolding comp_def
proof -
  fix x::nat assume "x > 0"
  then have "ln (real (x ^ c)) = c * ln (real x)"
    using ln_realpow by auto
  then have "ln (real (x ^ c)) ^ b = c ^ b * ln (real x) ^ b"
    by (simp add: semiring_normalization_rules(30))
oops

lemma bigTheta_compose_linear:
  fixes f1  g1 :: "nat\<Rightarrow>real" and f2 :: "nat \<Rightarrow> nat"
  assumes "stablebigO g1" "event_mono g1"
    and "f1 \<in> \<Theta>(g1)" "f2 \<in> \<Theta>(%n. n)"
  shows "(\<lambda>n. f1 (f2 n)) \<in> \<Theta>(g1)"
proof -   
  from assms(4) have g: "(\<lambda>x. real (f2 x)) \<in> \<omega>(\<lambda>n. 1)"
    by (metis (full_types) eventually_at_top_linorder eventually_nat_real filterlim_at_top filterlim_at_top_iff_smallomega landau_omega.small.in_cong_bigtheta) 
  have z: "g1 o (\<lambda>n. n) = g1" by auto
  have "f1 o f2 \<in> \<Theta>(g1 o (%n. n))"
    apply(rule bigTheta_compose)
    using assms g by auto
  thus ?thesis unfolding z comp_def .
qed

lemma bigTheta_compose_linear':
  fixes f1 g1 :: "nat\<Rightarrow>real" and f2 :: "nat \<Rightarrow> nat"
  assumes "stablebigO g1" "event_mono g1" "f1 \<in> \<Theta>(g1)" "f2 \<in> \<Theta>(polylog 1 0)"
  shows "(\<lambda>x. f1 (f2 x)) \<in> \<Theta>(g1)"
proof - 
  show ?thesis 
    apply (rule bigTheta_compose_linear)
    using assms unfolding polylog_def by auto
qed

section \<open>Asymptotic behaviour of arithmetic operations\<close>

lemma asym_bound_div:
  fixes c :: nat and f :: "nat \<Rightarrow> nat"
  shows "c > 0 \<Longrightarrow> f \<in> \<Omega>(\<lambda>n. n) \<Longrightarrow> f \<in> \<Theta>(g) \<Longrightarrow> (\<lambda>n. (f n) div c) \<in> \<Theta>(g)"
proof - 

  have estim: "\<And>x. x > c \<Longrightarrow> c>0 \<Longrightarrow> real (c*2) * real (x div c) \<ge> real (x)"
  proof -
    fix x::nat assume "x>c" "c>0"
    have "1 = c div c" using \<open>c>0\<close> by auto
    also have "\<dots> \<le> x div c" using \<open>x>c\<close> by(auto intro!: div_le_mono)
    finally have i: "1\<le>x div c" . 
    have "real x = real (x mod c + c * (x div c))" by simp
    also have "\<dots> = real (x mod c) + real (c * (x div c))" using of_nat_add by blast 
    also have "\<dots> \<le> real c + real c * real (x div c)" using \<open>c>0\<close> by auto
    also have "\<dots> \<le> real c * real (x div c) + real c * real (x div c)" using i \<open>0 < c\<close>  by auto
    also have "\<dots> = real (c*2) * real (x div c)" by auto
    finally show "real x \<le> real (c * 2) * real (x div c)" .
  qed

  have r: "\<And>a b c. c > 0 \<Longrightarrow> (a::real) \<ge> b / c \<Longrightarrow> b \<le> c * a"
    by (simp add: mult.commute pos_divide_le_eq) 

  assume c0: "c>0" 
  assume Om: "f \<in> \<Omega>(\<lambda>n. n)"
  assume "f \<in> \<Theta>(g)"
  then have O: "f \<in> O(g)" and Omega: "f \<in> \<Omega>(g)" by auto 
  then obtain c1 n where c1: "c1>0" and "\<forall>x\<ge>n. norm (f x) \<le> c1 * norm (g x)" using bigOE by blast
  then have f1: "\<And>x. x\<ge>n \<Longrightarrow> f x \<le> c1 * norm (g x)" by auto

  have O: "(\<lambda>n. (f n) div c) \<in> O(g)"
    apply(rule bigoI[where c="c1"])
    apply(rule eventually_sequentiallyI[where c="n"])
  proof -
    fix x assume a: "n\<le>x"
    have "norm (real (f x div c)) \<le> real (f x) " by simp
    also have "\<dots> \<le> c1 * norm (g x) " using f1[OF a] by (simp add: divide_right_mono) 
    finally show "norm (real (f x div c)) \<le> (c1 ) * norm (g x)" by auto
  qed

  from Omega obtain c1 n where c1: "c1>0" and "\<forall>x\<ge>n. norm (f x) \<ge> c1 * norm (g x)" using bigOmegaE by blast
  then have f1: "\<And>x. x\<ge>n \<Longrightarrow> f x \<ge> c1 * norm (g x)" by auto

  from Om fbig obtain n3 where P: "\<forall>x\<ge>n3. c+1 \<le> f x" by blast
  let ?n = "max n3 n"
  have Omega: "(\<lambda>n. (f n) div c) \<in> \<Omega>(g)"
    apply(rule bigomegaI[where c="real (c*2) / c1"])
    apply(rule eventually_sequentiallyI[where c="?n"])
  proof -
    fix x assume a: "?n\<le>x" 
    from a P have z1: "f x > c" by auto
    
    have "norm (g x) \<le> f x / c1" using f1  a      
      by (simp add: c1 mult_imp_le_div_pos le_divide_eq mult.commute)
    also have "\<dots> \<le> real (c*2) * real (f x div c) /c1" using estim z1 c0 by (simp add: c1 frac_le)        
    also have "\<dots> = ( real (c*2) / c1) * (f x div c)"  by auto
    also have "\<dots> = ( real (c*2) / c1) * norm (real (f x div c))" by auto
    finally show "norm (g x) \<le> (real (c*2) / c1)  * norm (real (f x div c))" .
  qed

  from Omega O show ?thesis by auto
qed

lemma asym_bound_div_linear:
  fixes c :: nat and f :: "nat \<Rightarrow> nat"
  shows "c > 0 \<Longrightarrow> f \<in> \<Theta>(\<lambda>n. real n) \<Longrightarrow> (\<lambda>n. real ((f n) div c)) \<in> \<Theta>(\<lambda>n. real n)"
  using asym_bound_div by auto 
 
lemma asym_bound_diff: 
  fixes f :: "nat \<Rightarrow> nat" and g :: "nat \<Rightarrow> nat"
  assumes "f \<in> \<Theta>(\<lambda>n. n)" "g \<in> \<Theta>(\<lambda>n. 1)"
  shows "(\<lambda>n. f n - g n) \<in> \<Theta>(\<lambda>n. n)"
proof -
  from assms(1) obtain c n where "c>0" and P: "\<forall>x\<ge>n. norm (f x) \<le> c * norm (x)" using bigOE by blast
  have O: "(\<lambda>n. f n - g n) \<in> O(\<lambda>n. n)"
    apply(rule bigoI[where c=c])
    apply(rule eventually_sequentiallyI[where c="n"])
    using P by auto

  from assms(2) have "g \<in> O(\<lambda>n. 1)" by auto
  from bigOE[OF this] obtain cg ng where "cg>0" and P: "\<forall>x\<ge>ng. norm (real (g x)) \<le> cg * norm ((\<lambda>n. 1::real) ng)" by blast
  then have g: "\<And>x. x\<ge>ng \<Longrightarrow> g x \<le> cg" by auto

  from assms(1) have fOm: "f \<in> \<Omega>(\<lambda>n. n)" by auto
  from bigOmegaE[OF this] obtain cf nf where cf: "cf>0" and "\<forall>x\<ge>nf. cf * norm (real x) \<le> norm (real (f x))" by blast
  then have f: "\<And>x. x\<ge>nf \<Longrightarrow> cf * x \<le> f x" by auto
  then have f: "\<And>x. x\<ge>nf \<Longrightarrow> x \<le> f x / cf" using cf
    by (simp add: mult.commute pos_le_divide_eq)  

  let ?n = "max (max nf ng) (nat \<lceil>2*cg/cf\<rceil>)"
  have Om: "(\<lambda>n. f n - g n) \<in> \<Omega>(\<lambda>n. n)"
  apply(rule bigomegaI[where c="(2/cf)"])
    apply(rule eventually_sequentiallyI[where c="?n"])
  proof -
    fix x assume n: "?n\<le>x" 
    have z1: "x\<ge>ng" using n by auto
    with g have  "g x \<le> cg" by auto
    then have g': "real (f x) - cg \<le> real (f x) - g x" by auto
    have z3: "x\<ge>nf" using n by auto

    have "x\<ge>2*cg/cf" using n by auto
    then have "x \<le> 2*(real x) - (2*cg/cf)" by linarith
    also have "\<dots> \<le> 2*(f x/cf) - (2*cg/cf)" using f[OF z3] by auto
    also have "\<dots> = 2/cf * (f x) - (2/cf)*cg" by auto
    also have "\<dots> = (2/cf) * (f x - cg)"  by (simp add: right_diff_distrib') 
    also have "\<dots> \<le> (2/cf) * (f x - g x)" apply(rule mult_left_mono) using g' cf  by auto
    also have "\<dots> = (2/cf) * norm (real (f x - g x)) " by auto
    finally 
    show "norm (real x) \<le> (2/cf) * norm (real (f x - g x)) " by auto
  qed

  from O Om show ?thesis by auto
qed

section \<open>Asymptotic behaviour of ceiling and log\<close>

lemma fixes f:: "nat\<Rightarrow>real" and g :: "nat \<Rightarrow> real" (* not possible to get rid of the event_nonneg premise, because of the nat cuttoff ! *)
  shows ceiling_Theta: "eventually_nonneg at_top f \<Longrightarrow> (\<lambda>n. g n) \<in> \<omega>(\<lambda>x. 1::real) \<Longrightarrow> (\<lambda>n. f n) \<in> \<Theta>(g) \<Longrightarrow> (\<lambda>n. real (nat \<lceil>f n\<rceil>)) \<in> \<Theta>(g)"
proof
  assume "(\<lambda>n. (g n)) \<in> \<omega>(\<lambda>x. 1::real)"
  from fsmall'[OF this,of 1]  obtain ng where ng: "\<forall>x\<ge>ng. 1 \<le> norm (g x)" by auto

  assume Th:"(\<lambda>n. f n) \<in> \<Theta>(g)"
  from Th have "(\<lambda>n. f n) \<in> O(g)" by auto
  then obtain n c where "c>0" and O: "\<forall>x\<ge>n. norm (f x) \<le> c * norm (g x)" using bigOE by blast

  let ?n = "max (nat\<lceil>ng\<rceil>) n" 

  show "(\<lambda>n. real (nat \<lceil>f n\<rceil>)) \<in> O(g)"
  proof (rule bigoI[where c="c+1"], rule eventually_sequentiallyI[where c="?n"])
    fix x assume "?n\<le>x"
    then have xn: "x\<ge>n" and xng: "x\<ge>ng" by auto
    have "norm (real (nat \<lceil>f x\<rceil>)) = real (nat \<lceil>f x\<rceil>)" by auto
    also have "\<dots> \<le> real (nat \<lceil>norm (f x)\<rceil>)"
      by (smt of_nat_0_less_iff real_norm_def zero_less_ceiling zero_less_nat_eq) 
    also have "\<dots> = of_int \<lceil>norm (f x)\<rceil>" by auto 
    also have "\<dots> \<le> norm (f x) + 1" by(rule of_int_ceiling_le_add_one)
    also have "\<dots> \<le> c * norm (g x) + 1 " using O xn by auto
    also have "\<dots> \<le> c * norm (g x) + norm (g x)" using ng xng by auto
    also have "\<dots> \<le> (c+1) * norm (g x)" by argo
    finally
    show "norm (real (nat \<lceil>f x\<rceil>)) \<le> (c+1) * norm (g x)" .
  qed

  assume  "eventually_nonneg at_top f"
  then have "\<forall>\<^sub>F n in at_top. f n \<ge> 0" unfolding eventually_nonneg_def by auto
  then obtain N where fpos: "\<And>n. n\<ge>N \<Longrightarrow>  f n \<ge> 0"  unfolding eventually_sequentially by auto

  from Th have "(\<lambda>n. f n) \<in> \<Omega>(g)" by auto
  then obtain n ::nat and  c where c: "c>0" and "\<forall>x\<ge>n. c * norm (g x) \<le> norm (f x)" using bigOmegaE by blast
  then have Om: "\<And>x. x\<ge>n \<Longrightarrow> norm (g x) \<le> norm (f x) / c "
    by (simp add: le_divide_eq mult.commute) 
  let ?n = "max N n"
  show "(\<lambda>n. real (nat \<lceil>f n\<rceil>)) \<in> \<Omega>(g)"
  proof (rule bigomegaI[where c="(1/c)"], rule eventually_sequentiallyI[where c="?n"]) 
    fix x assume x: "x\<ge>?n"
    with Om have "norm (g x) \<le> (1/c) * norm (f x)" by auto
    also have "\<dots> \<le> (1/c) * norm (real (nat \<lceil>f x\<rceil>))" apply(rule mult_left_mono) using c x fpos apply auto
      by (simp add: real_nat_ceiling_ge)  
    finally show "norm (g x) \<le> (1/c) * norm (real (nat \<lceil>f x\<rceil>))" .
  qed
qed

lemma eventually_nonneg_logplus: "c\<ge>0 \<Longrightarrow> eventually_nonneg sequentially (\<lambda>n. c *  log 2 (real (d + n)))"
  unfolding eventually_nonneg_def eventually_sequentially apply(rule exI[where x=1])
  unfolding log_def by auto

lemma log_2_asym': "(\<lambda>x::nat. real (f x)) \<in> \<Theta>(real) \<Longrightarrow> (\<lambda>n. log 2 (real (f n))) \<in> \<Theta>(ln)"
  apply(rule bigTheta_compose_linear[of _ "log 2"])
  apply(rule stablebigO_ln)
    apply(rule event_mono_ln)
  unfolding log_def by (auto simp add: asymp_equiv_imp_bigtheta asymp_equiv_plus_const_left)

lemma log_2_asym: "(\<lambda>n. log 2 (real (d + n))) \<in> \<Theta>(ln)"
  apply (rule log_2_asym')
  by (auto simp add: asymp_equiv_imp_bigtheta asymp_equiv_plus_const_left)
  
lemma abcd_lnx:
  assumes a: "a\<ge>0" and b: "b\<ge>1" and c: "c > 0" and d: "d \<ge> 0" shows "(\<lambda>n. a + b * real (nat \<lceil>c * log 2 (real (d + n))\<rceil>)) \<in> \<Theta>(\<lambda>x. ln (real x))"  (is "(\<lambda>n. a + ?f n) \<in> \<Theta>(?g)")
proof -  
  have "(\<lambda>n. log 2 (real (d + n))) \<in> \<Theta>(ln)" using log_2_asym by auto
  then have log_c: "(%n. c * log 2 (real (d + n))) \<in> \<Theta>(ln)" using c by auto

  have ceil: "(\<lambda>n. real (nat \<lceil>c * log 2 (real (d + n))\<rceil>)) \<in> \<Theta>(\<lambda>x. ln (real x))"
    apply(rule ceiling_Theta)
      apply(rule eventually_nonneg_logplus)  using c apply simp
    using log_c by auto

  then have ceil_b: "(\<lambda>n. b * real (nat \<lceil>c * log 2 (real (d + n))\<rceil>)) \<in> \<Theta>(\<lambda>x. ln (real x))" using b by auto

  have plusa: "\<Theta>(\<lambda>x. a + ?f x) = \<Theta>(?f)"
    apply(rule landau_theta.plus_absorb1)
    apply(rule landau_o.small.bigtheta_trans1'[OF _ ceil_b])
    by auto

  from ceil_b plusa  show ?thesis
    using bigtheta_sym by blast  
qed 

lemma log2_gt_zero: "x\<ge>1 \<Longrightarrow> log 2 x \<ge> 0" unfolding log_def using ln_gt_zero by auto


section \<open>Theta addition for any filter\<close>

lemma
  fixes f1 g1 f2 g2 :: "_ \<Rightarrow> real"
  assumes "eventually_nonneg F f1" "eventually_nonneg F  f2"
        "eventually_nonneg F  g1" "eventually_nonneg F  g2"
        "\<Theta>[F](f1) = \<Theta>[F](f2)" "\<Theta>[F](g1) = \<Theta>[F](g2)"
      shows Theta_plus: "\<Theta>[F](\<lambda>x. f1 x + g1 x) = \<Theta>[F](\<lambda>x. f2 x + g2 x)"
proof (rule landau_theta.cong_bigtheta, rule) 
  from assms have f: "f1 \<in> O[F](f2)" and g: "g1 \<in> O[F](g2)" by simp_all
  from f obtain cf where cf: "cf>0" and 1: "\<forall>\<^sub>F x in F. norm (f1 x) \<le> cf * norm (f2 x)"  using landau_o.bigE by blast
  from g obtain cg where cg: "cg>0" and 2: "\<forall>\<^sub>F x in F. norm (g1 x) \<le> cg * norm (g2 x)"  using landau_o.bigE by blast
  note B=  1 2 assms(2,4)[unfolded eventually_nonneg_def]

  show "(\<lambda>x. f1 x + g1 x) \<in> O[F](\<lambda>x. f2 x + g2 x)"
    apply(rule landau_o.bigI[where c="(max cf cg)"])
    using cf cg apply simp
    using B
  proof eventually_elim
    case (elim x)
    have un:  "norm (f1 x) \<le> (max cf cg) * norm (f2 x)" "norm (g1 x) \<le> (max cf cg) * norm (g2 x)"
       by (meson elim(1,2) dual_order.trans max.cobounded1  max.cobounded2 mult_right_mono norm_ge_zero)+
      
    have "norm (f1 x + g1 x) \<le> norm (f1 x) + norm (g1 x)" by (simp add: norm_triangle_ineq) 
    also have "\<dots> \<le>  (max cf cg) * norm (f2 x) + (max cf cg) * norm (g2 x)" using un by linarith
    also have "\<dots> = (max cf cg) * (norm (f2 x) + norm (g2 x))" by (simp add: distrib_left)      
    also have "\<dots> = (max cf cg) * norm (f2 x + g2 x)" using elim(3,4) by simp           
    finally show ?case . 
  qed 

  from assms have f: "f1 \<in> \<Omega>[F](f2)" and g: "g1 \<in> \<Omega>[F](g2)" by simp_all
  from f obtain cf where cf: "cf>0" and 1: "\<forall>\<^sub>F x in F. norm (f1 x) \<ge> cf * norm (f2 x)"  using landau_omega.bigE by blast
  from g obtain cg where cg: "cg>0" and 2: "\<forall>\<^sub>F x in F. norm (g1 x) \<ge> cg * norm (g2 x)"  using landau_omega.bigE by blast
  note B=1 2 assms(1,3)[unfolded eventually_nonneg_def]

  show "(\<lambda>x. f1 x + g1 x) \<in> \<Omega>[F](\<lambda>x. f2 x + g2 x)"
    apply(rule landau_omega.bigI[where c="(min cf cg)"])
    using cf cg apply simp
    using B
  proof eventually_elim
    case (elim x)
    have un:  "norm (f1 x) \<ge> (min cf cg) * norm (f2 x)" "norm (g1 x) \<ge> (min cf cg) * norm (g2 x)"
      by (meson elim(1,2) min.cobounded2 min.cobounded1 mult_le_cancel_right norm_ge_zero not_le order_trans)+
    
    have "min cf cg * norm (f2 x + g2 x) \<le> min cf cg * (norm (f2 x) + norm (g2 x))" apply(rule mult_left_mono)
      using cf cg by auto
    also have "\<dots> = (min cf cg) * norm (f2 x) + (min cf cg) * norm (g2 x)" by (simp add: distrib_left)
    also have "\<dots> \<le> norm (f1 x) + norm (g1 x)" using un by linarith        
    also have "\<dots> \<le> norm (f1 x + g1 x)" using elim(3,4) by auto
    finally show ?case .
  qed
qed

lemma
  fixes f1 g1 f2 g2 :: "_ \<Rightarrow> real"
  assumes "eventually_nonneg F f1" "eventually_nonneg F f2"
        "eventually_nonneg F g1" "eventually_nonneg F g2"
        "\<Theta>[F](f1) = \<Theta>[F](f2)" "\<Theta>[F](g1) = \<Theta>[F](g2)"
      shows Theta_plus': "\<Theta>[F](f1 + g1) = \<Theta>[F](f2 + g2)"
proof -
  have 1: "(\<lambda>x. f1 x + g1 x) = f1 + g1" by auto
  have 2: "(\<lambda>x. f2 x + g2 x) = f2 + g2" by auto
  show ?thesis using 1 2 Theta_plus[OF assms] by auto
qed


section \<open>Automation\<close>

lemma landau_norms:
  "real 1 = polylog 0 0 x"
  "real x = polylog 1 0 x"
  "ln x = polylog 0 1 x"
  "real (x ^ a) = polylog a 0 x"
  "(ln x) ^ b = polylog 0 b x"
  "polylog a1 b1 x * polylog a2 b2 x = polylog (a1 + a2) (b1 + b2) x"
  by (simp_all add: power_add polylog_def)

lemma plus_absorb1': "f \<in> o[F](g) \<Longrightarrow> \<Theta>[F](f + g) = \<Theta>[F](g)"
  unfolding plus_fun_def by (rule landau_theta.plus_absorb1)

lemma plus_absorb2': "g \<in> o[F](f) \<Longrightarrow> \<Theta>[F](f + g) = \<Theta>[F](f)"
  unfolding plus_fun_def by (rule landau_theta.plus_absorb2)

lemma plus_absorb_same': "\<Theta>[F](f + f) = \<Theta>[F](f)"
  unfolding plus_fun_def by auto

lemma bigtheta_add:
  assumes " eventually_nonneg F g1" " eventually_nonneg F g2"    
     "(\<lambda>x. real (f1 x)) \<in> \<Theta>[F](g1)" "(\<lambda>x. real (f2 x)) \<in> \<Theta>[F](g2)"
  shows "(\<lambda>x. real (f1 x + f2 x)) \<in> \<Theta>[F](g1 + g2)"
proof -
  have u: "g1 + g2 = (\<lambda>x. g1 x + g2 x)" by auto
  have "\<Theta>[F](\<lambda>x. real (f1 x) + real (f2 x)) = \<Theta>[F](\<lambda>x. g1 x + g2 x)"
    apply(rule Theta_plus) 
         apply(rule event_nonneg_real)
        apply fact
       apply(rule event_nonneg_real)
      apply fact
    using assms landau_theta.cong_bigtheta by blast+ 
  then show ?thesis by(simp add: u)
qed

lemma landau_norm_linear:
  "polylog 1 0 = real" unfolding polylog_def by auto

lemma landau_norm_const:
  "polylog 0 0 = (\<lambda>x::nat. 1::real)" unfolding polylog_def by auto

lemma landau_norm_times:
  "polylog a1 a2 * polylog b1 b2 = polylog (a1 + b1) (a2 + b2)"
  unfolding times_fun_def by (subst landau_norms(6)) auto

lemma bigtheta_const:
  "c > 0 \<Longrightarrow> (\<lambda>x. real c) \<in> \<Theta>(polylog 0 0)"
  unfolding polylog_def by simp

lemma bigtheta_linear:
  "(\<lambda>x. real x) \<in> \<Theta>(polylog 1 0)"
  unfolding polylog_def by simp

lemma bigtheta_mult:
  "(\<lambda>x. real (f1 x)) \<in> \<Theta>[F](g1) \<Longrightarrow> (\<lambda>x. real (f2 x)) \<in> \<Theta>[F](g2) \<Longrightarrow>
   (\<lambda>x. real (f1 x * f2 x)) \<in> \<Theta>[F](g1 * g2)"
  unfolding times_fun_def
  apply (subst bigtheta_mult_eq_set_mult)
  unfolding set_mult_def by auto

ML_file "landau_util.ML"

attribute_setup asym_bound = \<open>setup_attrib LandauUtil.add_asym_bound\<close>

ML_file "master_theorem_wrapper.ML"

method_setup master_theorem2 = \<open>setup_master_theorem\<close>
  "automatically apply the Master theorem for recursive functions"

end
