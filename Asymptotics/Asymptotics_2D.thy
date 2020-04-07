theory Asymptotics_2D
  imports Akra_Bazzi.Akra_Bazzi_Method Asymptotics_1D
begin

abbreviation "O\<^sub>2(\<lambda>x. f x) \<equiv> O[at_top \<times>\<^sub>F at_top](\<lambda>x. f x)"
abbreviation "o\<^sub>2(\<lambda>x. f x) \<equiv> o[at_top \<times>\<^sub>F at_top](\<lambda>x. f x)"
abbreviation "\<Theta>\<^sub>2(\<lambda>x. f x) \<equiv> \<Theta>[at_top \<times>\<^sub>F at_top](\<lambda>x. f x)"
abbreviation "\<Omega>\<^sub>2(\<lambda>x. f x) \<equiv> \<Omega>[at_top \<times>\<^sub>F at_top](\<lambda>x. f x)"

section \<open>Normal form in two variables\<close>

definition polylog2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> real" where
  "polylog2 a b c d = (\<lambda>(n,m). polylog a b n * polylog c d m)"

lemma event_nonneg_polylog2: "eventually_nonneg (at_top \<times>\<^sub>F at_top) (polylog2 a b c d)"
  apply (simp add: polylog2_def)
  apply (simp only: eventually_nonneg_def case_prod_beta)
  apply (simp add: eventually_prod_sequentially)
  apply (rule exI[where x=1]) unfolding polylog_def by auto

section \<open>Stability in two variables\<close>

definition stablebigO2 :: "(nat \<times> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "stablebigO2 f = (\<forall>c>0. \<forall>d>0. (\<lambda>(x,y). f (c * x, d * y)) \<in> O\<^sub>2(f))"  

lemma stablebigO2I:
  assumes "\<And>c d. 0 < c \<Longrightarrow> 0 < d \<Longrightarrow> (\<lambda>x. f (c * (fst x), d * (snd x))) \<in> O\<^sub>2(f)"
  shows "stablebigO2 f"
proof -
  have u: "\<And>c d. (\<lambda>x. f (c * (fst x), d * (snd x))) = (\<lambda>(x,y). f (c * x, d * y))" by auto
  show ?thesis using assms unfolding stablebigO2_def u by simp
qed

lemma stablebigO2_mult:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "stablebigO f" and "stablebigO g"
  shows "stablebigO2 (\<lambda>(n,m). f n * g m)"
proof -
  from assms(1)[unfolded stablebigO_def] have f: "\<And>c. c>0 \<Longrightarrow> (\<lambda>x. f (c * x)) \<in> O(f)" by auto
  from assms(2)[unfolded stablebigO_def] have g: "\<And>d. d>0 \<Longrightarrow> (\<lambda>x. g (d * x)) \<in> O(g)" by auto

  show ?thesis unfolding stablebigO2_def
  proof (safe)
    fix c d :: nat assume "c>0" "d>0"
    with f g have f: "(\<lambda>x. f (c * x)) \<in> O(f)"
              and g: "(\<lambda>x. g (d * x)) \<in> O(g)" by auto
    from f obtain fc fn  where fc: "fc>0" and fO: "\<forall>x\<ge>fn. norm (f (c * x)) \<le> fc * norm (f x)" using bigOE by blast
    from g obtain gc gn  where gc: "gc>0" and gO: "\<forall>x\<ge>gn. norm (g (d * x)) \<le> gc * norm (g x)" using bigOE by blast
      
    let ?N = "max fn gn"
    show "(\<lambda>(x, y). f (c * x) * g (d * y)) \<in> O\<^sub>2 (\<lambda>(n, m). f n * g m)"
      apply(rule landau_o.bigI[where c="(fc*gc)"])
      subgoal using fc gc by simp
      unfolding eventually_prod_sequentially
      apply(rule exI[where x="?N"])
      proof safe
        fix n m :: nat assume ev: "?N\<le>m" "?N\<le>n"

        have "norm (f (c * n) * g (d * m)) = norm (f (c*n)) * norm (g (d*m))" by (metis norm_mult)
        also have "\<dots> \<le> (fc * norm (f n)) * norm (g (d*m))" apply(rule mult_right_mono)
          using fO ev by auto
        also have "\<dots> \<le> (fc * norm (f n)) * (gc * norm (g m))" apply(rule mult_left_mono)
          using gO ev fc by auto
        also have "\<dots> = (fc*gc) * norm (f n * g m)" using fc gc
          by (metis mult.commute mult.left_commute norm_mult) 
        finally show "norm (f (c * n) * g (d * m)) \<le> (fc*gc) * norm (f n * g m)" .
      qed      
  qed
qed

lemma stablebigO2D':
  assumes "stablebigO2 f" "d1>0"  "d2>0"
  obtains c where "c>0" "eventually (\<lambda>x. norm (f (d1*(fst x), d2*(snd x))) \<le> c * norm (f x)) (at_top \<times>\<^sub>F at_top)"
proof -
  from assms have "(\<lambda>(x,y). f (d1 * x, d2*y)) \<in> O\<^sub>2(f)" (is "?f : _") 
    unfolding stablebigO2_def by auto
  then obtain c where c0: "c>0" and "\<forall>\<^sub>F x in sequentially \<times>\<^sub>F sequentially. norm (case x of (x, y) \<Rightarrow> f (d1 * x, d2 * y)) \<le> c * norm (f x)" 
    using landau_o.bigE by blast
  then have "eventually (\<lambda>x.  norm (f (d1*(fst x), d2*(snd x))) \<le> c *  norm (f x)) (at_top\<times>\<^sub>Fat_top)"
    using eventually_mono by fastforce 
  with c0 show ?thesis by (rule that)
qed

lemma stablebigO2D:
  assumes "stablebigO2 f" "d1>0"  "d2>0"
  obtains c where "c>0" "eventually (\<lambda>(x,y). norm (f (d1*x, d2*y)) \<le> c *  norm (f (x,y))) (at_top \<times>\<^sub>F at_top)"
proof -
  from assms have "(\<lambda>(x,y). f (d1 * x, d2*y)) \<in> O\<^sub>2(f)" (is "?f : _")
    unfolding stablebigO2_def by auto
  then obtain c where c0: "c>0" and "\<forall>\<^sub>F x in sequentially \<times>\<^sub>F sequentially. norm (case x of (x, y) \<Rightarrow> f (d1 * x, d2 * y)) \<le> c * norm (f x)" 
    using landau_o.bigE by blast
  then have "eventually (\<lambda>(x,y).  norm (f (d1*x, d2*y)) \<le> c *  norm (f (x,y))) (at_top\<times>\<^sub>Fat_top)"
    using eventually_mono by fastforce 
  with c0 show ?thesis by (rule that)
qed

lemma stablebigO2_plus:
  fixes f g :: "(nat*nat) \<Rightarrow> real"
  assumes f: "stablebigO2 f" and g: "stablebigO2 g" and
     evf: "eventually_nonneg (at_top \<times>\<^sub>F at_top) f" and
     evg: "eventually_nonneg (at_top \<times>\<^sub>F at_top) g"
  shows "stablebigO2 (f + g)"
proof (rule stablebigO2I)
  fix d1 d2 :: nat assume d: "d1>0"   "d2>0"
  from f d obtain cf where "cf>0" and f: "eventually (\<lambda>x.  norm (f (d1*(fst x), d2*(snd x))) \<le> cf *  norm (f x)) (sequentially\<times>\<^sub>Fsequentially)" 
    using stablebigO2D' by blast
  from g d obtain cg where "cg>0" and g: "eventually (\<lambda>x.  norm (g (d1*(fst x), d2*(snd x))) \<le> cg *  norm (g x)) (sequentially\<times>\<^sub>Fsequentially)" 
    using stablebigO2D' by blast
  have evf: "eventually (\<lambda>x. f x \<ge> 0) (at_top \<times>\<^sub>F at_top)" using evf by (simp add: eventually_nonneg_def)
  have evg: "eventually (\<lambda>x. g x \<ge> 0) (at_top \<times>\<^sub>F at_top)" using evg by (simp add: eventually_nonneg_def)

  let ?c = "max cf cg"

  show "(\<lambda>x. (f + g) (d1 * fst x, d2 * snd x)) \<in> O\<^sub>2 (f + g)"   
   apply(rule bigoI[where c="max cf cg"]) using f g evf evg
  proof (eventually_elim)
    case (elim x)
    then have nf: "norm (f x + g x) = norm (f x)+ norm (g x)" by auto

    have "norm ((f+g)(d1*(fst x), d2*(snd x))) = norm(f (d1*(fst x), d2*(snd x))+g (d1*(fst x), d2*(snd x)))" by auto
    also have "\<dots> \<le>  norm(f (d1*(fst x), d2*(snd x))) + norm (g (d1*(fst x), d2*(snd x)))"
      by (simp add: norm_triangle_ineq) 
    also have "\<dots> \<le> cf * norm (f x) + cg * norm (g x)" using elim(1,2) by auto
    also have "\<dots> \<le> ?c * norm (f x) + ?c * norm (g x)"
      by (simp add: max_def mult_right_mono)
    also have "\<dots> = ?c * (norm (f x)+ norm (g x))"
      by (simp add: distrib_left) 
    also have "\<dots> = ?c * norm (f x + g x)" unfolding nf by auto
    finally show ?case by simp
  qed
qed

lemma stable_polylog2: "stablebigO2 (polylog2 a b c d)"
  apply (simp add: polylog2_def)
  apply (rule stablebigO2_mult)
   apply (rule stable_polylog)
   apply (rule stable_polylog)
  done

section \<open>Eventual monotonicity in two variables\<close>

definition event_mono2 :: "((nat*nat) \<Rightarrow> real) \<Rightarrow> bool" where
  "event_mono2 g1 = eventually (\<lambda>(x1,y1). \<forall>x2\<ge>x1. \<forall>y2\<ge>y1. norm (g1 (x1,y1)) \<le> norm (g1 (x2,y2))) (at_top \<times>\<^sub>F at_top)"

lemma event_mono2_mult:
  assumes f: "event_mono f" and g: "event_mono g"
  shows "event_mono2 (\<lambda>(x,y). f x * g y)"
proof -
  note B=eventually_prodI[OF f[unfolded event_mono_def] g[unfolded event_mono_def]]
  { fix x :: "nat * nat"
    assume a: "(\<forall>x2\<ge>fst x. norm (f (fst x)) \<le> norm (f x2))" 
    assume b: "(\<forall>x2\<ge>snd x. norm (g (snd x)) \<le> norm (g x2))"
    have "\<forall>x2\<ge>fst x. \<forall>y2\<ge>snd x. norm (f (fst x) * g (snd x)) \<le> norm (f x2 * g y2)"
    proof safe
      fix x2 assume x2: "x2\<ge>fst x" 
      fix y2 assume y2: "y2\<ge>snd x" 
      have "norm (f (fst x) * g (snd x)) \<le> norm (f (fst x)) * norm (g (snd x))" 
        by (metis norm_mult order_refl)          
      also have "\<dots> \<le> norm (f x2) * norm (g (snd x))" apply(rule mult_right_mono)
          using a x2 by auto
      also have "\<dots> \<le> norm (f x2) * norm (g y2)" apply(rule mult_left_mono)
        using b y2 by auto  
      also have "\<dots> = (norm (f x2 * g y2))" by (metis norm_mult)  
      finally show "norm (f (fst x) * g (snd x)) \<le> norm (f x2 * g y2)" .
    qed
  } note A = this

  show ?thesis unfolding event_mono2_def
    apply(rule eventually_mono[OF B _])
      using A by auto
qed

lemma event_mono2_polylog2: "event_mono2 (polylog2 a b c d)"
  apply (simp add: polylog2_def)
  apply (rule event_mono2_mult)
   apply (rule event_mono_polylog)
   apply (rule event_mono_polylog)
  done

lemma event_mono2_plus:
  assumes f : "event_mono2 f" and g: "event_mono2 g" and
     evf: "eventually_nonneg (at_top \<times>\<^sub>F at_top) f" and
     evg: "eventually_nonneg (at_top \<times>\<^sub>F at_top) g"
  shows "event_mono2 (f + g)"
proof -
  have "eventually (\<lambda>x. f x \<ge> 0) (at_top \<times>\<^sub>F at_top)" using evf by (simp add: eventually_nonneg_def)
  then have evf: "eventually (\<lambda>x. \<forall>x2 y2. x2\<ge>fst x \<and> y2\<ge>snd x \<longrightarrow> f (x2,y2) \<ge> 0) (at_top \<times>\<^sub>F at_top)" 
    unfolding eventually_prod_sequentially apply auto  subgoal for N apply(rule exI[where x=N]) by auto done
  have "eventually (\<lambda>x. g x \<ge> 0) (at_top \<times>\<^sub>F at_top)" using evg by (simp add: eventually_nonneg_def)
  then have evg: "eventually (\<lambda>x. \<forall>x2 y2. x2\<ge>fst x \<and> y2\<ge>snd x \<longrightarrow> g (x2,y2) \<ge> 0) (at_top \<times>\<^sub>F at_top)" 
    unfolding eventually_prod_sequentially apply auto  subgoal for N apply(rule exI[where x=N]) by auto done
 
  note prem = evf f[unfolded event_mono2_def] g[unfolded event_mono2_def] evg

  show ?thesis
    unfolding event_mono2_def plus_fun_def
    using prem
  proof eventually_elim
    case (elim x)
    show "case x of (x1, y1) \<Rightarrow> \<forall>x2\<ge>x1. \<forall>y2\<ge>y1. norm (f (x1, y1) + g (x1, y1)) \<le> norm (f (x2, y2) + g (x2, y2))"
    proof safe
      fix x1 y1 x2 y2 assume x_eq: "x = (x1, y1)" and x2: "x1 \<le> x2" and y2: "y1 \<le> y2"
      with elim(1,4) have e: "f (x2, y2) \<ge> 0" "g (x2, y2) \<ge> 0" by force+
      have "norm (f (x1, y1) + g (x1, y1)) \<le> norm (f (x1, y1)) + norm (g (x1, y1))" by (simp add: norm_triangle_ineq) 
      also have "\<dots> \<le> norm (f (x2, y2)) + norm (g (x2, y2))" using elim(2,3) x_eq x2 y2 by fastforce
      also have "\<dots> = norm (f (x2, y2) + g (x2, y2))" using e by simp
      finally show "norm (f (x1, y1) + g (x1, y1)) \<le> norm (f (x2, y2) + g (x2, y2))" .
    qed
  qed
qed

section \<open>Auxiliary lemmas\<close>

lemma bigO2E:
  fixes f :: "nat \<times> nat \<Rightarrow> real"
  assumes "f \<in> O\<^sub>2(g)"
  obtains c n where "c > 0" "\<And>x. fst x\<ge>n \<Longrightarrow> snd x\<ge>n \<Longrightarrow> norm (f x) \<le> c * norm (g x)"
proof -
  from assms obtain c where c1: "c>0" and
      "\<forall>\<^sub>F x in (at_top\<times>\<^sub>Fat_top). norm (f x) \<le> c * norm (g x)" using landau_o.bigE by blast
  then obtain n where f1: "\<And>x. fst x\<ge>n \<Longrightarrow> snd x \<ge>n \<Longrightarrow> norm (f x) \<le> c * norm (g x)"
    unfolding eventually_prod_sequentially apply auto by blast   
  from c1 and f1 show ?thesis by (rule that)
qed 

lemma bigOmega2E:
  fixes f :: "(nat*nat) \<Rightarrow> real"
  assumes "f \<in> \<Omega>\<^sub>2(g)"
  obtains c n where "c > 0" "\<And>x. fst x\<ge>n \<Longrightarrow> snd x\<ge>n \<Longrightarrow> norm (f x) \<ge> c * norm (g x)"
proof -
  from assms obtain c where c1: "c>0" and
      "\<forall>\<^sub>F x in (at_top\<times>\<^sub>Fat_top). norm (f x) \<ge> c * norm (g x)" using landau_omega.bigE by blast
  then obtain n where f1: "\<And>x. fst x\<ge>n \<Longrightarrow> snd x \<ge>n \<Longrightarrow> norm (f x) \<ge> c * norm (g x)"
    unfolding eventually_prod_sequentially apply auto by blast   
  from c1 and f1 show ?thesis by (rule that)
qed 

section \<open>Composition in the two variable case\<close>

lemma mult_bivariate_I:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "f \<in> \<Theta>(\<lambda>n. n)"
  shows "(\<lambda>(n,m). real (f (n*m))) \<in> \<Theta>\<^sub>2(\<lambda>(n,m). real (n * m))" (is "?f \<in> \<Theta>[?F](?g)")
proof 
  from assms have O: "f \<in> O(\<lambda>n. n)" and Om: "f\<in>\<Omega>(\<lambda>n. n)" by auto

  from O obtain CO NO where "\<And>x. x\<ge>NO \<Longrightarrow> norm (f x) \<le> CO * norm (x)"
    using bigOE by blast
  then have O': "\<And>x y. x*y\<ge>NO \<Longrightarrow> real (f (x*y)) \<le> CO * (real x * real y)" by fastforce
  
  show "?f \<in> O[?F](?g)"
    apply(rule bigoI[where c=CO])
    apply(simp only: eventually_prod_sequentially)
    apply(rule exI[where x="NO+1"])
    apply auto apply(rule O')
    using nat_le_prod_with_le by auto 

  from Om obtain CO NO where c0: "CO > 0" and "\<And>x. x\<ge>NO \<Longrightarrow> CO * norm x \<le> norm (f x)"
    using bigOmegaE by blast
  then have "\<And>x y. x*y\<ge>NO \<Longrightarrow> CO * (real x * real y) \<le> real (f (x*y))" by fastforce
  then have Om': "\<And>x y. x*y\<ge>NO \<Longrightarrow> (real x * real y) \<le> real (f (x*y)) / CO"
    using c0 by (simp add: le_divide_eq mult.commute pos_le_divide_eq)  
  
  show "?f \<in> \<Omega>[?F](?g)"
    apply(rule bigomegaI[where c="(1/CO)"])
    apply(simp only: eventually_prod_sequentially)
    apply(rule exI[where x="NO+1"])
    apply auto apply (rule Om')
    using nat_le_prod_with_le by auto
qed

lemma bigO2_compose_both:
  fixes f1 :: "nat \<times> nat \<Rightarrow> nat" and f2a g2a f2b g2b:: "nat \<Rightarrow> nat"
  assumes "stablebigO2 g1"
    and "f1 \<in> O\<^sub>2(g1)"  
    and a: "f2a \<in> O(g2a)" "f2a \<in> \<omega>(\<lambda>n. 1)" "g2a \<in> \<omega>(\<lambda>n. 1)"
    and b: "f2b \<in> O(g2b)" "f2b \<in> \<omega>(\<lambda>n. 1)" "g2b \<in> \<omega>(\<lambda>n. 1)"
    and monog1: "eventually (\<lambda>(x1,y1). \<forall>x2\<ge>x1. \<forall>y2\<ge>y1. norm (g1 (x1,y1)) \<le> norm (g1 (x2,y2))) (at_top \<times>\<^sub>F at_top)"
  shows "(\<lambda>(x,y). f1 (f2a x, f2b y)) \<in> O\<^sub>2((\<lambda>(x,y). g1 (g2a x, g2b y)))"
proof -
  from assms(2) obtain c1 :: real and n1 :: nat where c1: "c1>0" and
      f1: "\<And>x. fst x\<ge>n1 \<Longrightarrow> snd x\<ge>n1 \<Longrightarrow> norm (f1 x) \<le> c1 * norm (g1 x)" using bigO2E  by blast 

  from a obtain c2a n2a :: nat where c2a: "c2a>0" and
      f2a: "\<And>x. x\<ge>n2a \<Longrightarrow> f2a x \<le> c2a * g2a x" using bigOE_nat by blast 
  from b obtain c2b n2b :: nat where c2b: "c2b>0" and
      f2b: "\<And>x. x\<ge>n2b \<Longrightarrow> f2b x \<le> c2b * g2b x" using bigOE_nat by blast 

  from assms(1) have "(\<lambda>(x, y). g1 (c2a * x, c2b* y)) \<in> O\<^sub>2 g1"
    unfolding stablebigO2_def using c2a c2b by blast
  from bigO2E[OF this] obtain c3 ::real and n3 :: nat where c3: "c3>0" and
    f3: "\<And>x. n3 \<le> fst x \<Longrightarrow> n3 \<le> snd x \<Longrightarrow> norm (case x of (x, y) \<Rightarrow> g1 (c2a * x, c2b * y)) \<le> c3 * norm (g1 x)" by blast
  then have
    f3: "\<And>x y. n3 \<le> x \<Longrightarrow> n3 \<le> y \<Longrightarrow> norm (g1 (c2a * x, c2b * y)) \<le> c3 * norm (g1 (x,y))" by auto

 (* note E=eventually_prodI[OF eventually_conj[OF fsmall_ev[OF a(2), of n1] fsmall_ev[OF a(3), of n3]]
        eventually_conj [OF fsmall_ev[OF b(2), of n1] fsmall_ev[OF b(3), of n3]]]
 *)
  from a fsmall obtain nf2a where nf2a: "\<forall>x\<ge>nf2a. n1 \<le> f2a x" by fast
  from a fsmall obtain ng2a where ng2a: "\<forall>x\<ge>ng2a. n3 \<le> g2a x" by fast

  from b fsmall obtain nf2b where nf2b: "\<forall>x\<ge>nf2b. n1 \<le> f2b x" by fast
  from b fsmall obtain ng2b where ng2b: "\<forall>x\<ge>ng2b. n3 \<le> g2b x" by fast

  from monog1 obtain nM where"\<forall>y1\<ge>nM. \<forall>x1\<ge>nM. \<forall>x2\<ge>x1. \<forall>y2\<ge>y1. norm (g1 (x1, y1)) \<le> norm (g1 (x2, y2))" 
    unfolding eventually_prod_sequentially by blast
  then have monog1: "\<And>x1 y1 x2 y2. x1 \<ge> nM \<Longrightarrow> y1 \<ge> nM \<Longrightarrow> x2\<ge>x1 \<Longrightarrow> y2\<ge>y1 \<Longrightarrow> norm (g1 (x1, y1)) \<le> norm (g1 (x2, y2))"
    by auto

  from a fsmall obtain nf3a where nf3a: "\<forall>x\<ge>nf3a. nM \<le> f2a x" by fast
  from b fsmall obtain nf3b where nf3b: "\<forall>x\<ge>nf3b. nM \<le> f2b x" by fast

  let ?n = "max (max nf2a nf2b) (max (max ng2a ng2b) (max (max nf3a nf3b) (max nM (max n3 (max (max n2a n2b) n1)))))"

  show ?thesis
    apply (rule bigoI[where c="c1 * c3"])
    unfolding eventually_prod_sequentially
    apply (rule exI[where x="?n"])
  proof safe
    fix n m :: nat 
    assume n: "?n\<le>n"
    have z1a: "n1 \<le> f2a n" using n nf2a by auto
    have z3a: "n3 \<le> g2a n" using n ng2a by auto
    assume m: "?n\<le>m"                       
    have z1b: "n1 \<le> f2b m" using m nf2b by auto 
    have z3b: "n3 \<le> g2b m" using m ng2b by auto

    have "norm (real (f1 (f2a n, f2b m))) \<le> c1 * norm (g1 (f2a n, f2b m))"
      apply (rule f1)  using z1a z1b m by auto
    also { have " norm (g1 (f2a n, f2b m)) \<le> norm (g1 (c2a * g2a n, c2b * g2b m))"
      apply (rule monog1) using f2a f2b nf3a nf3b n m by auto 
    also have "\<dots> \<le> c3 * norm (g1 (g2a n, g2b m))"
      apply (rule f3) using z3a z3b by auto
    finally have " c1 * norm (g1 (f2a n, f2b m)) \<le> c1 * (c3 * norm (g1 (g2a n, g2b m)))"
      using c1 by auto  }
    finally have "norm (real (f1 (f2a n, f2b m))) \<le> (c1 * c3) * (norm (g1 (g2a n, g2b m)))" by auto
    then show "norm (real (f1 (f2a n, f2b m))) \<le> c1 * c3 * norm (g1 (g2a n, g2b m))"
      using of_nat_mono by fastforce 
  qed
qed

lemma bigOmega2_compose_both:
  fixes f1 :: "nat \<times> nat \<Rightarrow> nat" and f2a g2a f2b g2b :: "nat \<Rightarrow> nat"
  assumes "stablebigO2 g1"
    and "f1 \<in> \<Omega>\<^sub>2(g1)" 
    and a: "f2a \<in> \<Omega>(g2a)" "f2a \<in> \<omega>(\<lambda>n. 1)" "g2a \<in> \<omega>(\<lambda>n. 1)"
    and b: "f2b \<in> \<Omega>(g2b)" "f2b \<in> \<omega>(\<lambda>n. 1)" "g2b \<in> \<omega>(\<lambda>n. 1)"  
    and monog1: "eventually (\<lambda>(x1,y1). \<forall>x2\<ge>x1. \<forall>y2\<ge>y1. norm (g1 (x1,y1)) \<le> norm (g1 (x2,y2))) (at_top \<times>\<^sub>F at_top)"
  shows "(\<lambda>(x,y). f1 (f2a x,f2b y)) \<in> \<Omega>\<^sub>2((\<lambda>(x,y). g1 (g2a x,g2b y)))"
proof - 
  from assms(2) obtain c1 and n1 :: nat where c1: "c1>0" 
      and f1: "\<And>x. fst x\<ge>n1 \<Longrightarrow> snd x\<ge>n1 \<Longrightarrow> norm (f1 x) \<ge> c1 * norm (g1 x)" using bigOmega2E  by blast 

  then have f1:  "\<And>x. fst x\<ge>n1 \<Longrightarrow> snd x\<ge>n1 \<Longrightarrow> norm (g1 x) \<le>norm (f1 x) / c1" using c1
    by (simp add: mult.commute pos_le_divide_eq)                                                

  from a obtain c2a n2a :: nat where c2a: "c2a>0" and
      f2a: "\<And>x. x \<ge> n2a \<Longrightarrow> g2a x \<le> c2a * f2a x" using bigOmegaE_nat by blast
  from b obtain c2b n2b :: nat where c2b: "c2b>0" and
      f2b: "\<And>x. x \<ge> n2b \<Longrightarrow> g2b x \<le> c2b * f2b x" using bigOmegaE_nat by blast

  from assms(1) have "(\<lambda>(x, y). g1 (c2a * x,c2b * y)) \<in> O\<^sub>2 g1"
    unfolding stablebigO2_def using c2a c2b by blast
  from bigO2E[OF this] obtain c3 ::real and n3 :: nat where c3: "c3>0" and
    f3: "\<And>x. n3 \<le> fst x \<Longrightarrow> n3 \<le> snd x \<Longrightarrow> norm (case x of (x, y) \<Rightarrow> g1 (c2a * x,c2b * y)) \<le> c3 * norm (g1 x)" by blast
  then have
    f3: "\<And>x y. n3 \<le> x \<Longrightarrow> n3 \<le> y \<Longrightarrow> norm (g1 (c2a * x,c2b * y)) \<le> c3 * norm (g1 (x,y))" by auto

  from monog1 obtain nM where"\<forall>y1\<ge>nM. \<forall>x1\<ge>nM. \<forall>x2\<ge>x1. \<forall>y2\<ge>y1. norm (g1 (x1, y1)) \<le> norm (g1 (x2, y2))"
    unfolding eventually_prod_sequentially by blast
  then have monog1: "\<And>x1 y1 x2 y2. x1 \<ge> nM \<Longrightarrow> y1 \<ge> nM \<Longrightarrow> x2\<ge>x1 \<Longrightarrow>y2\<ge>y1 \<Longrightarrow> norm (g1 (x1, y1)) \<le> norm (g1 (x2, y2))"
    by auto

  from a fsmall obtain nf2a where nf2a: "\<forall>x\<ge>nf2a. n1 \<le> f2a x" by force
  from a fsmall obtain ng2a where ng2a: "\<forall>x\<ge>ng2a. n3 \<le> f2a x" by force
  from a fsmall obtain ng3a where ng3a: "\<forall>x\<ge>ng3a. nM \<le> g2a x" by fast
  from b fsmall obtain nf2b where nf2b: "\<forall>x\<ge>nf2b. n1 \<le> f2b x" by force
  from b fsmall obtain ng2b where ng2b: "\<forall>x\<ge>ng2b. n3 \<le> f2b x" by force
  from b fsmall obtain ng3b where ng3b: "\<forall>x\<ge>ng3b. nM \<le> g2b x" by fast

  let ?n = "max (max nf2a nf2b) (max (max ng2a ng2b) (max nM (max (max ng3a ng3b) (max n1 (max (max n2a n2b) n3)))))"

  show ?thesis
    apply (rule bigomegaI[where c="c3/c1"])
    unfolding eventually_prod_sequentially
    apply (rule exI[where x="?n"])
  proof safe
    fix n m :: nat
    assume n: "?n\<le>n"
    have z1a: "n1 \<le> f2a n" using n nf2a by auto
    have z2a: "n2a \<le> n"  using n   by auto
    have z3a: "n3 \<le> f2a n"  using n ng2a by auto 
    have z4a: "nM \<le> g2a n" using ng3a n by auto
    assume m: "?n\<le>m"
    have z1b: "n1 \<le> f2b m" using m nf2b by auto
    have z2b: "n2b \<le>m "  using m   by auto
    have z3b: "n3 \<le> f2b m"  using m ng2b by auto 
    have z4b: "nM \<le> g2b m" using ng3b m by auto

    have za: "g2a n \<le> c2a * f2a n" using f2a z2a by auto
    have zb: "g2b m \<le> c2b * f2b m" using f2b z2b by auto
    have "norm ( (g1 (g2a n,g2b m))) \<le> norm (g1 (c2a * f2a n,c2b * f2b m))"
      apply (rule monog1) using n m za zb z4a z4b by auto
    also have "\<dots> \<le> c3 * norm (g1 (f2a n, f2b m))" apply(rule f3) using  z3a z3b by auto
    also have "\<dots> \<le> c3 * (norm (f1 (f2a n, f2b m))/c1)" apply(rule mult_left_mono) apply(rule f1)
       using c3 z1a z1b by auto 
    also have "\<dots> = (c3/c1) * norm (f1 (f2a n, f2b m))" by auto
    finally show "norm (g1 (g2a n, g2b m)) \<le> c3 / c1 * norm (real (f1 (f2a n, f2b m)))" by auto
  qed
qed 

lemma bigTheta2_compose_both:
 fixes f1 :: "nat \<times> nat \<Rightarrow> nat" and f2a g2a f2b g2b :: "nat \<Rightarrow> nat"
  assumes "stablebigO2 g1"
    and "f1 \<in> \<Theta>\<^sub>2(g1)"
    and a: "f2a \<in> \<Theta>(g2a)" "f2a \<in> \<omega>(\<lambda>n. 1)"   
    and b: "f2b \<in> \<Theta>(g2b)" "f2b \<in> \<omega>(\<lambda>n. 1)"   
    and monog1: "eventually (\<lambda>(x1,y1). \<forall>x2\<ge>x1. \<forall>y2\<ge>y1. norm (g1 (x1,y1)) \<le> norm (g1 (x2,y2))) (at_top \<times>\<^sub>F at_top)"
  shows "(\<lambda>(x,y). f1 (f2a x,f2b y)) \<in> \<Theta>\<^sub>2((\<lambda>(x,y). g1 (g2a x,g2b y)))"
proof -
  from a have a': "g2a \<in> \<omega>(\<lambda>n. 1)"
    using landau_omega.small.in_cong_bigtheta by blast 
  from b have b': "g2b \<in> \<omega>(\<lambda>n. 1)"
    using landau_omega.small.in_cong_bigtheta by blast 
  have "(\<lambda>(x,y). f1 (f2a x,f2b y)) \<in> O\<^sub>2((\<lambda>(x,y). g1 (g2a x,g2b y)))"
    apply (rule bigO2_compose_both) using assms a' b'  by auto 
  moreover have "(\<lambda>(x,y). f1 (f2a x, f2b y)) \<in> \<Omega>\<^sub>2((\<lambda>(x,y). g1 (g2a x, g2b y)))"
    apply (rule bigOmega2_compose_both) using assms a' b' by auto
  ultimately show ?thesis by auto
qed

lemma bigTheta2_compose_both_linear:
 fixes f1 :: "nat \<times> nat \<Rightarrow>nat" and f2a f2b :: "nat \<Rightarrow> nat"
  assumes "stablebigO2 g1" "event_mono2 g1"
    and "f1 \<in> \<Theta>\<^sub>2(g1)"
    and a: "f2a \<in> \<Theta>(%n. n)"  and b: "f2b \<in> \<Theta>(%n. n)"   
  shows "(\<lambda>(x,y). f1 (f2a x,f2b y)) \<in> \<Theta>\<^sub>2(g1)"
proof -
  from a have a': "f2a \<in> \<omega>(\<lambda>n. 1)"
    by (metis (full_types) bigthetaD2 eventually_at_top_linorder eventually_nat_real
          filterlim_at_top filterlim_at_top_iff_smallomega landau_flip(4) landau_trans(41)) 
  
  from b have b': "f2b \<in> \<omega>(\<lambda>n. 1)"
    by (metis (full_types) bigthetaD2 eventually_at_top_linorder eventually_nat_real
          filterlim_at_top filterlim_at_top_iff_smallomega landau_flip(4) landau_trans(41)) 

  have "(\<lambda>(x,y). f1 (f2a x,f2b y)) \<in> \<Theta>\<^sub>2((\<lambda>(x,y). g1 (x, y)))"
    apply(rule bigTheta2_compose_both)
    using assms a' b' unfolding event_mono2_def by auto
  then show ?thesis by auto
qed

lemma bigTheta2_compose_both_linear':
  fixes f1 :: "nat \<times> nat \<Rightarrow> nat" and f2a f2b :: "nat \<Rightarrow> nat"
  assumes "stablebigO2 g1" "event_mono2 g1" "f1 \<in> \<Theta>\<^sub>2(g1)" "f2a \<in> \<Theta>(polylog 1 0)" "f2b \<in> \<Theta>(polylog 1 0)"
  shows "(\<lambda>x. real (f1 (f2a (fst x), f2b (snd x)))) \<in> \<Theta>\<^sub>2(g1)"
proof -
  have 1: "(\<lambda>x. real (f1 (f2a (fst x), f2b (snd x)))) = (\<lambda>(x,y). (f1 (f2a x, f2b y)))" by auto
  have 2: "(\<lambda>(x,y). (f1 (f2a x, f2b y))) \<in> \<Theta>\<^sub>2(g1)"
    apply (rule bigTheta2_compose_both_linear)
    using assms unfolding polylog_def by auto
  then show ?thesis using 1 2 by auto
qed 

section \<open>Small O, big O domination on two variables\<close>

lemma oO_o:
  fixes f1 f2 g1 g2 :: "nat \<Rightarrow> real"
  assumes "f1 \<in> o(g1)"  "f2 \<in> O(g2)"
  shows "(\<lambda>(n,m). f1 n * f2 m) \<in> o\<^sub>2(\<lambda>(n,m). g1 n * g2 m)"
proof (rule landau_o.smallI)
  fix c :: real assume c: "0 < c"
  thm landau_o.smallD  landau_o.smallI 
  from assms(2) obtain c2 where c2: "c2>0" and 2: "\<forall>\<^sub>F x in at_top. norm (f2 x) \<le> c2 * norm (g2 x)" using landau_o.bigE by blast
  have 1: "\<forall>\<^sub>F x in at_top. norm (f1 x) \<le> (c/c2) * norm (g1 x)" apply(rule landau_o.smallD)
    using assms(1) c2 c by auto
  note B=eventually_prodI[OF 1 2]
  show "\<forall>\<^sub>F x in sequentially \<times>\<^sub>F sequentially. norm (case x of (n, m) \<Rightarrow> f1 n * f2 m) \<le> c * norm (case x of (n, m) \<Rightarrow> g1 n * g2 m)"
  proof (rule eventually_mono[OF B _], safe, simp)
    fix n m 
    assume 1: "\<bar>f1 n\<bar> \<le> c * \<bar>g1 n\<bar> / c2" and 2: "\<bar>f2 m\<bar> \<le> c2 * \<bar>g2 m\<bar>"
    have "\<bar>f1 n * f2 m\<bar> = \<bar>f1 n\<bar> * \<bar>f2 m\<bar>" using abs_mult by blast  
    also have "\<dots> \<le> (c*\<bar>g1 n\<bar>/c2) * \<bar>f2 m\<bar>" apply(rule mult_right_mono) apply fact by simp
    also have "\<dots> \<le> (c*\<bar>g1 n\<bar>/c2) * (c2* \<bar>g2 m\<bar>)" apply(rule mult_left_mono) apply fact using c c2 by simp
    also have "\<dots> = c * \<bar>g1 n * g2 m\<bar>" using c2 by (simp add: abs_mult) 
    finally show "\<bar>f1 n * f2 m\<bar> \<le> c * \<bar>g1 n * g2 m\<bar>" .
  qed
qed

lemma Oo_o:
  fixes f1 f2 g1 g2 :: "nat \<Rightarrow> real"
  assumes "f1 \<in> O(g1)"  "f2 \<in> o(g2)"
  shows "(\<lambda>(n,m). f1 n * f2 m) \<in> o\<^sub>2(\<lambda>(n,m). g1 n * g2 m)"
proof (rule landau_o.smallI)
  fix c :: real assume c: "0 < c"
  thm landau_o.smallD  landau_o.smallI 
  from assms(1) obtain c1 where c2: "c1>0" and 1: "\<forall>\<^sub>F x in at_top. norm (f1 x) \<le> c1 * norm (g1 x)" using landau_o.bigE by blast
  have 2: "\<forall>\<^sub>F x in at_top. norm (f2 x) \<le> (c/c1) * norm (g2 x)" apply(rule landau_o.smallD)
    using assms(2) c2 c by auto
  note B=eventually_prodI[OF 1 2]
  show "\<forall>\<^sub>F x in sequentially \<times>\<^sub>F sequentially. norm (case x of (n, m) \<Rightarrow> f1 n * f2 m) \<le> c * norm (case x of (n, m) \<Rightarrow> g1 n * g2 m)"
  proof (rule eventually_mono[OF B _], safe, simp)
    fix n m 
    assume 2: "\<bar>f2 m\<bar> \<le> c * \<bar>g2 m\<bar> / c1" and 1: "\<bar>f1 n\<bar> \<le> c1 * \<bar>g1 n\<bar>"
    have "\<bar>f1 n * f2 m\<bar> = \<bar>f1 n\<bar> * \<bar>f2 m\<bar>" using abs_mult by blast  
    also have "\<dots> \<le> \<bar>f1 n\<bar> * (c * \<bar>g2 m\<bar> / c1)" apply(rule mult_left_mono) apply fact by simp
    also have "\<dots> \<le> (c1 * \<bar>g1 n\<bar>) * (c * \<bar>g2 m\<bar> / c1)" apply(rule mult_right_mono) apply fact using c c2 by simp
    also have "\<dots> = c * \<bar>g1 n * g2 m\<bar>" using c2 by (simp add: abs_mult) 
    finally show "\<bar>f1 n * f2 m\<bar> \<le> c * \<bar>g1 n * g2 m\<bar>" .
  qed
qed

section "2D Theta bound for product of 1D Theta bounds"

lemma mult_Theta_bivariate:
  fixes f1 f2 :: "nat \<Rightarrow> nat" and g1 g2 :: "nat \<Rightarrow> real"
  assumes "f1 \<in> \<Theta>(\<lambda>n. g1 n)" "f2 \<in> \<Theta>(\<lambda>n. g2 n)"
  shows "(\<lambda>(n, m). f1 n * f2 m) \<in> \<Theta>\<^sub>2(\<lambda>(n, m). g1 n * g2 m)"
proof 
  thm landau_o.bigE landau_omega.bigE
  from assms have 1: "f1 : O(\<lambda>n. g1 n)" and 2: "f2 \<in> O(\<lambda>n. g2 n)" by auto
  from 1 obtain cf where cf: "cf>0" and 1: "\<forall>\<^sub>F x in at_top. norm (f1 x) \<le> cf * norm (g1 x)" using landau_o.bigE by blast
  from 2 obtain cg where cg: "cg>0" and 2: "\<forall>\<^sub>F x in at_top. norm (f2 x) \<le> cg * norm (g2 x)" using landau_o.bigE by blast

  note B=eventually_prodI[OF 1 2]
  show "(\<lambda>(n, m). f1 n * f2 m) \<in> O\<^sub>2(\<lambda>(n, m). g1 n * g2 m)"
    apply(rule landau_o.bigI[where c="cf*cg"])
    using cf cg apply simp
  proof (rule eventually_mono[OF B _], safe, simp)
    fix n m 
    assume "real (f1 n) \<le> cf * \<bar>g1 n\<bar>"
    assume "real (f2 m) \<le> cg * \<bar>g2 m\<bar>"
    have "real (f1 n) * real (f2 m) \<le> (cf * \<bar>g1 n\<bar>) * real (f2 m)"
      apply(rule mult_right_mono) apply fact by simp
    also have "\<dots> \<le> (cf * \<bar>g1 n\<bar>) * (cg * \<bar>g2 m\<bar>)"
      apply(rule mult_left_mono) apply fact using cf by simp
    also have "\<dots> = (cf*cg) * \<bar>g1 n * g2 m\<bar>" by(simp add: abs_mult) 
    finally show "real (f1 n) * real (f2 m) \<le> cf * cg * \<bar>g1 n * g2 m\<bar>" .
  qed
  from assms have 1: "f1 : \<Omega>(\<lambda>n.  (g1 n))" and 2: "f2 \<in> \<Omega>(\<lambda>n.  (g2 n))" by auto
  from 1 obtain cf where cf: "cf>0" and 1: "\<forall>\<^sub>F x in at_top. norm (f1 x) \<ge> cf * norm (g1 x)" using landau_omega.bigE by blast
  from 2 obtain cg where cg: "cg>0" and 2: "\<forall>\<^sub>F x in at_top. norm (f2 x) \<ge> cg * norm (g2 x)" using landau_omega.bigE by blast

  note B=eventually_prodI[OF 1 2]
  show "(\<lambda>(n, m). f1 n * f2 m) \<in> \<Omega>\<^sub>2(\<lambda>(n, m). g1 n * g2 m)"
    apply(rule landau_omega.bigI[where c="cf*cg"])
    using cf cg apply simp
  proof (rule eventually_mono[OF B _], safe, simp)
    fix n m 
    assume "real (f1 n) \<ge> cf * \<bar>g1 n\<bar>"
    assume "real (f2 m) \<ge> cg * \<bar>g2 m\<bar>"
    have "(cf*cg) * \<bar>g1 n * g2 m\<bar> = (cf * \<bar>g1 n\<bar>) * (cg * \<bar>g2 m\<bar>)" by(simp add: abs_mult)
    also have "\<dots> \<le> (cf * \<bar>g1 n\<bar>) * real (f2 m)"
      apply (rule mult_left_mono) apply fact using cf by simp
    also have "\<dots> \<le> real (f1 n) * real (f2 m)"  
      apply (rule mult_right_mono) apply fact by simp
    finally show "real (f1 n) * real (f2 m) \<ge> cf * cg * \<bar>g1 n * g2 m\<bar>" .
  qed
qed

section \<open>Comparison between polylog2 functions\<close>
 
definition "cas1 a1 b1 c1 d1 a2 b2 c2 d2 = (((a1<a2 \<or> a1=a2 \<and> b1<b2) \<and> (c1<c2 \<or> c1=c2 \<and> d1\<le>d2))
     \<or> ((a1<a2 \<or> a1=a2 \<and> b1\<le>b2) \<and> (c1<c2 \<or> c1=c2 \<and> d1<d2)))"

lemma polylog2_compare:
  assumes "f1 \<in> \<Theta>\<^sub>2(polylog2 a1 b1 c1 d1)" "f2 \<in> \<Theta>\<^sub>2(polylog2 a2 b2 c2 d2)"
  shows "cas1 a1 b1 c1 d1 a2 b2 c2 d2 \<Longrightarrow> f1 \<in> o\<^sub>2(f2)" (* other case is symmetric *)
proof -
  assume "cas1 a1 b1 c1 d1 a2 b2 c2 d2"
  then have AoB: "((a1<a2 \<or> a1=a2 \<and> b1<b2) \<and> (c1<c2 \<or> c1=c2 \<and> d1\<le>d2))
     \<or>   ((a1<a2 \<or> a1=a2 \<and> b1\<le>b2) \<and> (c1<c2 \<or> c1=c2 \<and> d1<d2))  " (is "?A \<or> ?B") unfolding cas1_def by auto
  show "f1 \<in> o\<^sub>2(f2)"
  proof (cases "?A")
    case True
    then have o: "polylog a1 b1 \<in> o(polylog a2 b2)" 
        and O: "polylog c1 d1 \<in> O(polylog c2 d2)" 
      unfolding polylog_def apply auto
      apply(cases "d1=d2") apply auto
      apply(cases "d1=d2") by auto

    have "polylog2 a1 b1 c1 d1 \<in> o\<^sub>2(polylog2 a2 b2 c2 d2)" unfolding polylog2_def
      by(rule oO_o[OF o O]) 
    then show ?thesis using assms  
      using landau_o.small.cong_ex_bigtheta by blast 
  next
    case False
    with AoB have B: "?B" by simp
    then have O: "polylog a1 b1 \<in> O(polylog a2 b2)" 
        and o: "polylog c1 d1 \<in> o(polylog c2 d2)" 
      unfolding polylog_def apply auto
      apply(cases "b1=b2") apply auto
      apply(cases "b1=b2") by auto

    have "polylog2 a1 b1 c1 d1 \<in> o\<^sub>2(polylog2 a2 b2 c2 d2)" unfolding polylog2_def
      by(rule Oo_o[OF O o]) 
    then show ?thesis using assms  
      using landau_o.small.cong_ex_bigtheta by blast  
  qed
qed

lemma polylog2_compare':
  assumes "(a1<a2 \<or> a1=a2 \<and> b1<b2) \<and> (c1<c2 \<or> c1=c2 \<and> d1\<le>d2)"
  shows "polylog2 a1 b1 c1 d1 \<in> o\<^sub>2(polylog2 a2 b2 c2 d2)"
proof -
  have 1: "cas1 a1 b1 c1 d1 a2 b2 c2 d2" using assms cas1_def by metis
  have 2: "polylog2 a1 b1 c1 d1 \<in> \<Theta>\<^sub>2(polylog2 a1 b1 c1 d1)" by auto
  have 3: "polylog2 a2 b2 c2 d2 \<in> \<Theta>\<^sub>2(polylog2 a2 b2 c2 d2)" by auto 
  show ?thesis using polylog2_compare(1)[OF 2 3 1] by simp
qed

lemma polylog2_compare2':
  assumes "(a1<a2 \<or> a1=a2 \<and> b1\<le>b2) \<and> (c1<c2 \<or> c1=c2 \<and> d1<d2)"
  shows "polylog2 a1 b1 c1 d1 \<in> o\<^sub>2(polylog2 a2 b2 c2 d2)"
proof -
  have 1: "cas1 a1 b1 c1 d1 a2 b2 c2 d2" using assms cas1_def by metis
  have 2: "polylog2 a1 b1 c1 d1 \<in> \<Theta>\<^sub>2(polylog2 a1 b1 c1 d1)" by auto
  have 3: "polylog2 a2 b2 c2 d2 \<in> \<Theta>\<^sub>2(polylog2 a2 b2 c2 d2)" by auto 
  show ?thesis using polylog2_compare(1)[OF 2 3 1] by simp
qed

section \<open>Setup for automation\<close>

lemma landau_norms2:
  "polylog a1 b1 (fst x) = polylog2 a1 b1 0 0 x"
  "polylog a2 b2 (snd x) = polylog2 0 0 a2 b2 x"
  "polylog2 a1 b1 a2 b2 x * polylog2 a3 b3 a4 b4 x = polylog2 (a1 + a3) (b1 + b3) (a2 + a4) (b2 + b4) x"
  apply (metis (no_types, lifting) Groups.add_ac(2) landau_norms(1) landau_norms(4) landau_norms(5)
         landau_norms(6) polylog2_def polylog_def prod.collapse prod.simps(2))
  apply (metis (no_types, lifting) Groups.add_ac(2) landau_norms(1) landau_norms(4) landau_norms(5)
         landau_norms(6) polylog2_def polylog_def prod.collapse prod.simps(2))
  by (smt landau_norms(6) polylog2_def semiring_normalization_rules(13) split_beta)

lemma landau_norms2':
  "polylog2 a1 b1 a2 b2 * polylog2 a3 b3 a4 b4 = polylog2 (a1 + a3) (b1 + b3) (a2 + a4) (b2 + b4)"
  using landau_norms2(3) by auto

lemma mult_Theta_bivariate':
  assumes "(\<lambda>x. real (f1 x)) \<in> \<Theta>(polylog a b)"
    "(\<lambda>x. real (f2 x)) \<in> \<Theta>(polylog c d)"
  shows "(\<lambda>x. real (f1 (fst x) * f2 (snd x))) \<in> \<Theta>\<^sub>2 (polylog2 a b c d)"
proof -
  have 1: "(\<lambda>x. real (case x of (n, m) \<Rightarrow> f1 n * f2 m)) \<in> \<Theta>\<^sub>2 (\<lambda>x. case x of (n, m) \<Rightarrow> polylog a b n * polylog c d m)"
    using mult_Theta_bivariate[of f1 "polylog a b" f2 "polylog c d"] assms by auto
  then show ?thesis
    unfolding polylog2_def by (simp add: case_prod_beta)
qed

lemma mult_Theta_bivariate1:
  assumes "(\<lambda>x. real (f1 x)) \<in> \<Theta>(polylog a b)"
  shows "(\<lambda>x. real (f1 (fst x))) \<in> \<Theta>\<^sub>2 (polylog2 a b 0 0)"
proof -
  have 1: "(\<lambda>x. real (f1 (fst x))) = (\<lambda>x. real (f1 (fst x) * 1))" by auto
  with assms show ?thesis
    apply (subst 1) apply (rule mult_Theta_bivariate')
     apply auto
    apply (subst of_nat_1 [symmetric]) apply (rule bigtheta_const) by auto
qed

lemma mult_Theta_bivariate2:
  assumes "(\<lambda>x. real (f2 x)) \<in> \<Theta>(polylog a b)"
  shows "(\<lambda>x. real (f2 (snd x))) \<in> \<Theta>\<^sub>2 (polylog2 0 0 a b)"
proof -
  have 1: "(\<lambda>x. real (f2 (snd x))) = (\<lambda>x. real (1 * f2 (snd x)))" by auto
  with assms show ?thesis
    apply (subst 1) apply (rule mult_Theta_bivariate')
     apply auto
    apply (subst of_nat_1 [symmetric]) apply (rule bigtheta_const) by auto
qed

lemma polylog_omega1:
  "a \<noteq> 0 \<or> b \<noteq> 0 \<Longrightarrow> polylog a b \<in> \<omega>(\<lambda>x. 1::real)" unfolding polylog_def by auto

ML_file "landau_util_2d.ML"

end
