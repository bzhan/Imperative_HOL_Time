(* The development here follows Separation_Logic_Imperative_HOL
   (by Lammich and Meis) in the AFP *)

theory SepAuto
  imports "../../auto2/HOL/Auto2_Main" "../Imperative_HOL"
begin

section {* Partial Heaps *}

datatype pheap = pHeap (heapOf: heap) (addrOf: "addr set") (timeOf: nat)
setup {* add_rewrite_rule_back @{thm pheap.collapse} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm pheap.simps(1)}) *}
setup {* fold add_rewrite_rule @{thms pheap.sel} *}

fun in_range :: "(heap \<times> addr set) \<Rightarrow> bool" where
  "in_range (h,as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup {* add_rewrite_rule @{thm in_range.simps} *}

(* Two heaps agree on a set of addresses. *)
definition relH :: "addr set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" where [rewrite]:
  "relH as h h' = (in_range (h, as) \<and> in_range (h', as) \<and>
     (\<forall>t. \<forall>a\<in>as. refs h t a = refs h' t a \<and> arrays h t a = arrays h' t a))"

lemma relH_dist_union [forward]:
  "relH (as \<union> as') h h' \<Longrightarrow> relH as h h' \<and> relH as' h h'" by auto2

lemma relH_ref [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_ref r \<in> as \<Longrightarrow> Ref.get h r = Ref.get h' r"
  by (simp add: Ref.get_def relH_def)

lemma relH_array [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_array r \<in> as \<Longrightarrow> Array.get h r = Array.get h' r"
  by (simp add: Array.get_def relH_def)

lemma relH_set_ref [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_ref r}} h (Ref.set r x h)"
  by (simp add: Ref.set_def relH_def)

lemma relH_set_array [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_array r}} h (Array.set r x h)"
  by (simp add: Array.set_def relH_def)

section {* Assertions *}

datatype assn_raw = Assn (assn_fn: "pheap \<Rightarrow> bool")

fun aseval :: "assn_raw \<Rightarrow> pheap \<Rightarrow> bool" where
  "aseval (Assn f) h = f h"
setup {* add_rewrite_rule @{thm aseval.simps} *}

definition proper :: "assn_raw \<Rightarrow> bool" where [rewrite]:
  "proper P = (
    (\<forall>h as n. aseval P (pHeap h as n) \<longrightarrow> in_range (h,as)) \<and>
    (\<forall>h h' as n. aseval P (pHeap h as n) \<longrightarrow> relH as h h' \<longrightarrow> in_range (h',as) \<longrightarrow> aseval P (pHeap h' as n)))"
setup {* add_property_const @{term proper} *}

fun in_range_assn :: "pheap \<Rightarrow> bool" where
  "in_range_assn (pHeap h as n) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup {* add_rewrite_rule @{thm in_range_assn.simps} *} 

typedef assn = "Collect proper"
@proof @have "Assn in_range_assn \<in> Collect proper" @qed

setup {* add_rewrite_rule @{thm Rep_assn_inject} *}
setup {* register_wellform_data ("Abs_assn P", ["proper P"]) *}
setup {* add_prfstep_check_req ("Abs_assn P", "proper P") *}

lemma Abs_assn_inverse' [rewrite]: "proper y \<Longrightarrow> Rep_assn (Abs_assn y) = y"
  by (simp add: Abs_assn_inverse)

lemma proper_Rep_assn [forward]: "proper (Rep_assn P)" using Rep_assn by auto

definition models :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Turnstile>" 50) where [rewrite_bidir]:
  "h \<Turnstile> P \<longleftrightarrow> aseval (Rep_assn P) h"

lemma models_in_range [resolve]: "pHeap h as n \<Turnstile> P \<Longrightarrow> in_range (h,as)" by auto2

lemma mod_relH [forward]: "relH as h h' \<Longrightarrow> pHeap h as n \<Turnstile> P \<Longrightarrow> pHeap h' as n \<Turnstile> P" by auto2

instantiation assn :: one begin
definition one_assn :: assn where [rewrite]:
  "1 \<equiv> Abs_assn (Assn (\<lambda>h. timeOf h = 0 \<and> addrOf h = {}))"
instance .. end

abbreviation one_assn :: assn ("emp") where "one_assn \<equiv> 1"

lemma one_assn_rule [rewrite]: "h \<Turnstile> emp \<longleftrightarrow> timeOf h = 0 \<and> addrOf h = {}" by auto2
setup {* del_prfstep_thm @{thm one_assn_def} *}

section \<open>Definition of $\<close>
  
definition timeCredit_assn :: "nat \<Rightarrow> assn" ("$") where [rewrite]:
  "timeCredit_assn n = Abs_assn (Assn (\<lambda>h. timeOf h = n \<and> addrOf h = {}))"
    
lemma timeCredit_assn_rule [rewrite]: "h \<Turnstile> $n \<longleftrightarrow> timeOf h = n \<and> addrOf h = {}" by auto2
setup {* del_prfstep_thm @{thm timeCredit_assn_def} *}

instantiation assn :: times begin
definition times_assn where [rewrite]:
  "P * Q = Abs_assn (Assn (
    \<lambda>h. (\<exists>as1 as2 n1 n2. addrOf h = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and> timeOf h = n1 + n2 \<and>
         aseval (Rep_assn P) (pHeap (heapOf h) as1 n1) \<and> aseval (Rep_assn Q) (pHeap (heapOf h) as2 n2))))"
instance .. end

lemma mod_star_convE [backward]:
  "pHeap h as n \<Turnstile> A * B \<Longrightarrow>
   \<exists>as1 as2 n1 n2. as = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and> n = n1 + n2 \<and> pHeap h as1 n1 \<Turnstile> A \<and> pHeap h as2 n2 \<Turnstile> B" by auto2

lemma mod_star_convI [backward]:
  "as1 \<inter> as2 = {} \<Longrightarrow> pHeap h as1 n1 \<Turnstile> A \<Longrightarrow> pHeap h as2 n2 \<Turnstile> B \<Longrightarrow>
   pHeap h (as1 \<union> as2) (n1 + n2) \<Turnstile> A * B" by auto2
setup {* del_prfstep_thm @{thm times_assn_def} *}

lemma aseval_ext [backward]: "\<forall>h. aseval P h = aseval P' h \<Longrightarrow> P = P'"
  apply (cases P) apply (cases P') by auto

lemma assn_ext: "\<forall>h as n. pHeap h as n \<Turnstile> P \<longleftrightarrow> pHeap h as n \<Turnstile> Q \<Longrightarrow> P = Q"
@proof @have "Rep_assn P = Rep_assn Q" @qed
setup {* add_backward_prfstep_cond @{thm assn_ext} [with_filt (order_filter "P" "Q")] *}

setup {* del_prfstep_thm @{thm aseval_ext} *}

lemma assn_one_left: "emp * P = (P::assn)"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> P \<longleftrightarrow> pHeap h as n \<Turnstile> emp * P" @with
    @case "pHeap h as n \<Turnstile> P" @with
      @have "as = {} \<union> as"
      @have "n = 0 + n"
    @end
    @case "pHeap h as n \<Turnstile> 1 * P" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> emp" "pHeap h as2 n2 \<Turnstile> P"
    @end
  @end
@qed

lemma assn_times_comm: "P * Q = Q * (P::assn)"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> P * Q \<longleftrightarrow> pHeap h as n \<Turnstile> Q * P" @with
    @case "pHeap h as n \<Turnstile> P * Q" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P" "pHeap h as2 n2 \<Turnstile> Q"
      @have "as = as2 \<union> as1" @have "n = n2 + n1"
    @end
    @case "pHeap h as n \<Turnstile> Q * P" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> Q" "pHeap h as2 n2 \<Turnstile> P"
      @have "as = as2 \<union> as1" @have "n = n2 + n1"
    @end
  @end
@qed

lemma assn_times_assoc: "(P * Q) * R = P * (Q * (R::assn))"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> (P * Q) * R \<longleftrightarrow> pHeap h as n \<Turnstile> P * (Q * R)" @with
    @case "pHeap h as n \<Turnstile> (P * Q) * R" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P * Q" "pHeap h as2 n2 \<Turnstile> R"
      @obtain as11 as12 n11 n12 where
        "as1 = as11 \<union> as12" "as11 \<inter> as12 = {}" "n1 = n11 + n12" "pHeap h as11 n11 \<Turnstile> P" "pHeap h as12 n12 \<Turnstile> Q"
      @have "pHeap h (as12 \<union> as2) (n12 + n2) \<Turnstile> Q * R"
      @have "as = as11 \<union> (as12 \<union> as2)" @have "n = n11 + (n12 + n2)"
    @end
    @case "pHeap h as n \<Turnstile> P * (Q * R)" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P" "pHeap h as2 n2 \<Turnstile> (Q * R)"
      @obtain as21 as22 n21 n22 where
        "as2 = as21 \<union> as22" "as21 \<inter> as22 = {}" "n2 = n21 + n22" "pHeap h as21 n21 \<Turnstile> Q" "pHeap h as22 n22 \<Turnstile> R"
      @have "pHeap h (as1 \<union> as21) (n1 + n21) \<Turnstile> P * Q"
      @have "as = (as1 \<union> as21) \<union> as22" @have "n = (n1 + n21) + n22"
    @end
  @end
@qed

instantiation assn :: comm_monoid_mult begin
  instance apply standard
  apply (rule assn_times_assoc) apply (rule assn_times_comm) by (rule assn_one_left)
end

subsection {* Existential Quantification *}

definition ex_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>A" 11) where [rewrite]:
  "(\<exists>\<^sub>Ax. P x) = Abs_assn (Assn (\<lambda>h. \<exists>x. h \<Turnstile> P x))"

lemma mod_ex_dist [rewrite]: "(h \<Turnstile> (\<exists>\<^sub>Ax. P x)) \<longleftrightarrow> (\<exists>x. h \<Turnstile> P x)" by auto2
setup {* del_prfstep_thm @{thm ex_assn_def} *}

lemma ex_distrib_star: "(\<exists>\<^sub>Ax. P x * Q) = (\<exists>\<^sub>Ax. P x) * Q"
@proof
  @have "\<forall>h as n. pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q \<longleftrightarrow> pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x * Q)" @with
    @case "pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q" @with
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> (\<exists>\<^sub>Ax. P x)" "pHeap h as2 n2 \<Turnstile> Q"
      @obtain x where "pHeap h as1 n1 \<Turnstile> P x"
      @have "pHeap h as n \<Turnstile> P x * Q"
    @end
    @case "pHeap h as n \<Turnstile> (\<exists>\<^sub>Ax. P x * Q)" @with
      @obtain x where "pHeap h as n \<Turnstile> P x * Q"
      @obtain as1 as2 n1 n2 where
        "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P x" "pHeap h as2 n2 \<Turnstile> Q"      
    @end
  @end
@qed

subsection {* Pointers *}

definition sngr_assn :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> assn" (infix "\<mapsto>\<^sub>r" 82) where [rewrite]:
  "r \<mapsto>\<^sub>r x = Abs_assn (Assn (
    \<lambda>h. timeOf h = 0 \<and> Ref.get (heapOf h) r = x \<and> addrOf h = {addr_of_ref r} \<and> addr_of_ref r < lim (heapOf h)))"

lemma sngr_assn_rule [rewrite]:
  "pHeap h as n \<Turnstile> r \<mapsto>\<^sub>r x \<longleftrightarrow>
      n = 0 \<and> Ref.get h r = x \<and> as = {addr_of_ref r} \<and> addr_of_ref r < lim h" by auto2
setup {* del_prfstep_thm @{thm sngr_assn_def} *}

definition snga_assn :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> assn" (infix "\<mapsto>\<^sub>a" 82) where [rewrite]:
  "r \<mapsto>\<^sub>a x = Abs_assn (Assn (
    \<lambda>h. timeOf h = 0 \<and> Array.get (heapOf h) r = x \<and> addrOf h = {addr_of_array r} \<and> addr_of_array r < lim (heapOf h)))"

lemma snga_assn_rule [rewrite]:
  "pHeap h as n \<Turnstile> r \<mapsto>\<^sub>a x \<longleftrightarrow>
      (n = 0 \<and> Array.get h r = x \<and> as = {addr_of_array r} \<and> addr_of_array r < lim h)" by auto2
setup {* del_prfstep_thm @{thm snga_assn_def} *}

subsection {* Pure Assertions *}

definition pure_assn :: "bool \<Rightarrow> assn" ("\<up>") where [rewrite]:
  "\<up>b = Abs_assn (Assn (\<lambda>h. addrOf h = {} \<and> timeOf h = 0 \<and> b))"

lemma pure_assn_rule [rewrite]: "h \<Turnstile> \<up>b \<longleftrightarrow> (addrOf h = {} \<and> timeOf h = 0 \<and> b)" by auto2
setup {* del_prfstep_thm @{thm pure_assn_def} *}

definition top_assn :: assn ("true") where [rewrite]:
  "top_assn = Abs_assn (Assn in_range_assn)"

lemma top_assn_rule [rewrite]: "pHeap h as n \<Turnstile> true \<longleftrightarrow> in_range (h, as)" by auto2
setup {* del_prfstep_thm @{thm top_assn_def} *}

setup {* del_prfstep_thm @{thm models_def} *}

subsection {* Properties of assertions *}

abbreviation bot_assn :: assn ("false") where "bot_assn \<equiv> \<up>False"

setup {* add_forward_prfstep @{thm mod_star_convE} *}

lemma mod_false' [resolve]: "\<not>(h \<Turnstile> false * R)" by auto2

lemma mod_star_trueI [backward]: "h \<Turnstile> P \<Longrightarrow> h \<Turnstile> P * true"
@proof
  @have "addrOf h = addrOf h \<union> {}"
  @have "timeOf h = timeOf h + 0"
@qed

lemma top_assn_reduce: "true * true = true" by auto2
setup {* del_prfstep_thm @{thm mod_star_trueI} *}

lemma sngr_same_false [resolve]: "\<not> h \<Turnstile> p \<mapsto>\<^sub>r x * p \<mapsto>\<^sub>r y * Qu" by auto2

lemma mod_pure_star_dist [rewrite]:
  "h \<Turnstile> P * \<up>b \<longleftrightarrow> h \<Turnstile> P \<and> b"
@proof
  @case "h \<Turnstile> P \<and> b" @with
    @have "addrOf h = addrOf h \<union> {}"
    @have "timeOf h = timeOf h + 0"
  @end
@qed
    
lemma mod_timeCredit_dest [rewrite]:
  "pHeap h as n \<Turnstile> P * $m \<longleftrightarrow> pHeap h as (n - m) \<Turnstile> P \<and> n \<ge> m"
@proof
  @case "pHeap h as (n - m) \<Turnstile> P \<and> n \<ge> m" @with
    @have "as = as \<union> {}"
    @have "n = (n - m) + m"
  @end  
@qed

lemma mod_pure': "h \<Turnstile> \<up>b \<longleftrightarrow> (h \<Turnstile> emp \<and> b)" by auto2
lemma pure_conj:  "\<up>(P \<and> Q) = \<up>P * \<up>Q" by auto2

subsection {* Theorems for time credits *}

lemma time_credit_add [resolve]: "$(m + n) = $m * $n" by auto2

subsection {* Entailment and its properties *}

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>A" 10) where [rewrite]:
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>h. h \<Turnstile> P \<longrightarrow> h \<Turnstile> Q)"

lemma entails_triv: "A \<Longrightarrow>\<^sub>A A" by auto2
lemma entails_true: "A \<Longrightarrow>\<^sub>A true" by auto2
lemma entail_equiv_forward: "P = Q \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q" by auto2
lemma entail_equiv_backward: "P = Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A P" by auto2
lemma entailsD [forward]: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P \<Longrightarrow> h \<Turnstile> Q" by auto2
lemma entailsD': "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P * R \<Longrightarrow> h \<Turnstile> Q * R" by auto2
lemma entailsD_back: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> \<not>h \<Turnstile> Q * R \<Longrightarrow> \<not>h \<Turnstile> P * R" by auto2
lemma entail_trans2: "A \<Longrightarrow>\<^sub>A D * B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C" by auto2
lemma entail_trans2': "D * B \<Longrightarrow>\<^sub>A A \<Longrightarrow> C \<Longrightarrow>\<^sub>A B \<Longrightarrow> D * C \<Longrightarrow>\<^sub>A A" by auto2
lemma entails_invD: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not>(h \<Turnstile> B) \<Longrightarrow> \<not>(h \<Turnstile> A)" by auto2

lemma gc_time: "a\<ge>b \<Longrightarrow> $a \<Longrightarrow>\<^sub>A $b * true"
@proof @have "$a = $b * $(a-b)" @qed

definition time_credit_ge :: "nat \<Rightarrow> nat \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 60) where
  "a \<ge>\<^sub>t b \<longleftrightarrow> a \<ge> b"
setup {* add_backward_prfstep (equiv_backward_th @{thm time_credit_ge_def}) *}

lemma gc_time': "a \<ge>\<^sub>t b \<Longrightarrow> h \<Turnstile> R * $(a + p) \<Longrightarrow> h \<Turnstile> R * $(b + p) * true"
  by (smt ab_semigroup_mult_class.mult_ac(1) entailsD' gc_time mult.commute time_credit_add time_credit_ge_def)

lemma gc_time'': "a \<ge>\<^sub>t b \<Longrightarrow> h \<Turnstile> $(a + p) \<Longrightarrow> h \<Turnstile> $(b + p) * true"
  by (smt add.commute add.right_neutral gc_time' time_credit_add)

section \<open>Setup for timeFrame\<close>
    
setup {* fold add_rewrite_rule @{thms timeFrame.simps} *}

lemma timeFrame_reduceNone [forward]: "timeFrame n f = None \<Longrightarrow> f = None" by auto2

lemma timeFrame_reduceSome [forward]: "timeFrame n f = (Some (r,h,t)) \<Longrightarrow> f = Some (r,h,t-n) \<and> t\<ge>n"
@proof @case "f = None" @qed

section {* Definition of the run predicate *}

inductive run :: "'a Heap \<Rightarrow> heap option \<Rightarrow> heap option \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "run c None None r n"
| "execute c h = None \<Longrightarrow> run c (Some h) None r n"
| "execute c h = Some (r, h', n) \<Longrightarrow> run c (Some h) (Some h') r n"
setup {* add_case_induct_rule @{thm run.cases} *}
setup {* fold add_resolve_prfstep @{thms run.intros(1,2)} *}
setup {* add_forward_prfstep @{thm run.intros(3)} *}
setup {* add_backward_prfstep @{thm run.intros(3)} *}

lemma run_preserve_None [forward]:
  "run c None \<sigma>' r n \<Longrightarrow> \<sigma>' = None"
@proof @case_induct "run c None \<sigma>' r n" @qed

lemma run_execute_fail [forward]:
  "execute c h = None \<Longrightarrow> run c (Some h) \<sigma>' r n \<Longrightarrow> \<sigma>' = None"
@proof @case_induct "run c (Some h) \<sigma>' r n" @qed

lemma run_execute_succeed [forward]:
  "execute c h = Some (r', h', n) \<Longrightarrow> run c (Some h) \<sigma>' r n' \<Longrightarrow> \<sigma>' = Some h' \<and> r = r' \<and> n=n'"
@proof @case_induct "run c (Some h) \<sigma>' r n'" @qed

lemma run_complete [resolve]:
  "\<exists>\<sigma>' r n. run c \<sigma> \<sigma>' (r::'a) n"
@proof
  @obtain "r::'a" where "r = r"
  @case "\<sigma> = None" @with @have "run c None None r 0" @end
  @case "execute c (the \<sigma>) = None" @with @have "run c \<sigma> None r 0" @end
@qed

lemma run_to_execute [forward]:
  "run c (Some h) \<sigma>' r n \<Longrightarrow> if \<sigma>' = None then execute c h = None else execute c h = Some (r, the \<sigma>', n)"
@proof @case_induct "run c (Some h) \<sigma>' r n" @qed

setup {* add_rewrite_rule @{thm execute_bind(1)} *}
lemma runE [forward]:
  "run f (Some h) (Some h') r' t1 \<Longrightarrow> run (f \<bind> g) (Some h) \<sigma> r t \<Longrightarrow> run (g r') (Some h') \<sigma> r (t-t1)"
  by auto2

setup {* add_rewrite_rule @{thm Array.get_alloc} *}
setup {* add_rewrite_rule @{thm Ref.get_alloc} *}
setup {* add_rewrite_rule_bidir @{thm Array.length_def} *}

section {* Definition of hoare triple, and the frame rule. *}

definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where [rewrite]:
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"

lemma new_addr_refl [rewrite]: "new_addrs h as h = as" by auto2

definition hoare_triple :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>") where [rewrite]:
  "<P> c <Q> \<longleftrightarrow> (\<forall>h as \<sigma> r n t. pHeap h as n \<Turnstile> P \<longrightarrow> run c (Some h) \<sigma> r t \<longrightarrow> 
    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n-t) \<Turnstile> Q r \<and> n\<ge>t \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and>
     lim h \<le> lim (the \<sigma>)))"

abbreviation hoare_triple' :: "assn \<Rightarrow> 'r Heap \<Rightarrow> ('r \<Rightarrow> assn) \<Rightarrow> bool" ("<_> _ <_>\<^sub>t") where
  "<P> c <Q>\<^sub>t \<equiv> <P> c <\<lambda>r. Q r * true>"

lemma frame_rule [backward]:
  "<P> c <Q> \<Longrightarrow> <P * R> c <\<lambda>x. Q x * R>"
@proof
  @have "\<forall>h as \<sigma> r n t. pHeap h as n \<Turnstile> P * R \<longrightarrow> run c (Some h) \<sigma> r t \<longrightarrow> 
                    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) (n-t) \<Turnstile> Q r * R \<and> n\<ge>t \<and>
                     relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>))" @with
    @obtain as1 as2 n1 n2 where
      "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "n = n1 + n2" "pHeap h as1 n1 \<Turnstile> P" "pHeap h as2 n2 \<Turnstile> R"
    @have "relH as2 h (the \<sigma>)"
    @have "new_addrs h as (the \<sigma>) = new_addrs h as1 (the \<sigma>) \<union> as2"
    @have "n - t = (n1 - t) + n2"
  @end
@qed

(* This is the last use of the definition of separating conjunction. *)
setup {* fold del_prfstep_thm [@{thm mod_star_convI}, @{thm mod_star_convE}] *}

lemma norm_pre_pure_iff: "<P * \<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <P> c <Q>)" by auto2
lemma norm_pre_pure_iff2: "<\<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <emp> c <Q>)" by auto2

section {* Hoare triples for atomic commands *}

(* First, those that do not modify the heap. *)
setup {* add_rewrite_rule @{thm execute_assert(1)} *}
lemma assert_rule:
  "<\<up>(R x) * $1> assert R x <\<lambda>r. \<up>(r = x)>" by auto2

lemma execute_return' [rewrite]: "execute (return x) h = Some (x, h, 1)" by (metis comp_eq_dest_lhs execute_return)
lemma return_rule:
  "<$1> return x <\<lambda>r. \<up>(r = x)>" by auto2

setup {* add_rewrite_rule @{thm execute_nth(1)} *}
lemma nth_rule:
  "<a \<mapsto>\<^sub>a xs * $1 * \<up>(i < length xs)> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i)>" by auto2

setup {* add_rewrite_rule @{thm execute_len} *}
lemma length_rule:
  "<a \<mapsto>\<^sub>a xs * $1> Array.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>" by auto2

setup {* add_rewrite_rule @{thm execute_lookup} *}
lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x * $1> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
    
setup {* add_rewrite_rule @{thm execute_freeze} *}
lemma freeze_rule:
  "<a \<mapsto>\<^sub>a xs * $(1 + length xs)> Array.freeze a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs)>" by auto2

(* Next, the update rules. *)
setup {* add_rewrite_rule @{thm Ref.lim_set} *}
lemma Array_lim_set [rewrite]: "lim (Array.set p xs h) = lim h" by (simp add: Array.set_def)

setup {* fold add_rewrite_rule [@{thm Ref.get_set_eq}, @{thm Array.get_set_eq}] *}
setup {* add_rewrite_rule @{thm Array.update_def} *}

setup {* add_rewrite_rule @{thm execute_upd(1)} *}
lemma upd_rule:
  "<a \<mapsto>\<^sub>a xs * $1 * \<up>(i < length xs)> Array.upd i x a <\<lambda>r. a \<mapsto>\<^sub>a list_update xs i x * \<up>(r = a)>" by auto2

setup {* add_rewrite_rule @{thm execute_update} *}
lemma update_rule:
  "<p \<mapsto>\<^sub>r y * $1> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>" by auto2

(* Finally, the allocation rules. *)
lemma lim_set_gen [rewrite]: "lim (h\<lparr>lim := l\<rparr>) = l" by simp

lemma Array_alloc_def' [rewrite]: 
  "Array.alloc xs h = (let l = lim h; r = Array l in (r, (Array.set r xs (h\<lparr>lim := l + 1\<rparr>))))"
  by (simp add: Array.alloc_def)

setup {* fold add_rewrite_rule [
  @{thm addr_of_array.simps}, @{thm addr_of_ref.simps}, @{thm Ref.alloc_def}] *}

lemma refs_on_Array_set [rewrite]: "refs (Array.set p xs h) t i = refs h t i"
  by (simp add: Array.set_def)

lemma arrays_on_Ref_set [rewrite]: "arrays (Ref.set p x h) t i = arrays h t i"
  by (simp add: Ref.set_def)

lemma refs_on_Array_alloc [rewrite]: "refs (snd (Array.alloc xs h)) t i = refs h t i"
  by (metis (no_types, lifting) Array.alloc_def refs_on_Array_set select_convs(2) snd_conv surjective update_convs(3))

lemma arrays_on_Ref_alloc [rewrite]: "arrays (snd (Ref.alloc x h)) t i = arrays h t i"
  by (metis (no_types, lifting) Ref.alloc_def arrays_on_Ref_set select_convs(1) sndI surjective update_convs(3))

lemma arrays_on_Array_alloc [rewrite]: "i < lim h \<Longrightarrow> arrays (snd (Array.alloc xs h)) t i = arrays h t i"
  by (smt Array.alloc_def Array.set_def addr_of_array.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less simps(1) snd_conv surjective update_convs(1) update_convs(3))

lemma refs_on_Ref_alloc [rewrite]: "i < lim h \<Longrightarrow> refs (snd (Ref.alloc x h)) t i = refs h t i"
  by (smt Ref.alloc_def Ref.set_def addr_of_ref.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less select_convs(2) simps(6) snd_conv surjective update_convs(3))

setup {* add_rewrite_rule @{thm execute_new} *}
lemma new_rule:
  "<$(n+1)> Array.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>" by auto2

setup {* add_rewrite_rule @{thm execute_of_list} *}
lemma of_list_rule:
  "<$ (1+length xs)> Array.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>" by auto2

setup {* add_rewrite_rule @{thm execute_ref} *}
lemma ref_rule:
  "<$1> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2

setup {* fold del_prfstep_thm [@{thm sngr_assn_rule}, @{thm snga_assn_rule}] *}
setup {* fold del_prfstep_thm [@{thm pure_assn_rule}, @{thm top_assn_rule},
  @{thm mod_pure_star_dist} , @{thm mod_timeCredit_dest}, @{thm timeCredit_assn_rule}] *}

section {* success_run and its properties. *}

lemma new_addrs_bind [rewrite]:
  "lim h \<le> lim h' \<Longrightarrow> lim h' \<le> lim h'' \<Longrightarrow> new_addrs h' (new_addrs h as h') h'' = new_addrs h as h''" by auto2

fun success_run :: "'a Heap \<Rightarrow> pheap \<Rightarrow> pheap \<Rightarrow> 'a \<Rightarrow> bool" where
  "success_run f (pHeap h as n1) (pHeap h' as' n2) r \<longleftrightarrow>
    as' = new_addrs h as h' \<and> run f (Some h) (Some h') r (n1-n2) \<and> n1\<ge>n2 \<and> relH {a. a < lim h \<and> a \<notin> as} h h' \<and> lim h \<le> lim h'"
setup {* add_rewrite_rule @{thm success_run.simps} *}

lemma success_run_bind:
  "success_run f h h' r \<Longrightarrow> success_run (g r) h' h'' r' \<Longrightarrow> success_run (f \<bind> g) h h'' r'" by auto2

lemma success_run_next: "success_run f h h'' r' \<Longrightarrow>
  \<forall>h'. \<sigma> = Some (heapOf h') \<and> success_run (f \<bind> g) h h' r \<longrightarrow> \<not> h' \<Turnstile> Q \<Longrightarrow>
  \<forall>h'. \<sigma> = Some (heapOf h') \<and> success_run (g r') h'' h' r \<longrightarrow> \<not> h' \<Turnstile> Q" by auto2

lemma hoare_triple_def' [rewrite]:
  "<P> c <Q> \<longleftrightarrow> (\<forall>h \<sigma> r t. h \<Turnstile> P \<longrightarrow> run c (Some (heapOf h)) \<sigma> r t \<longrightarrow>
    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs (heapOf h) (addrOf h) (the \<sigma>)) (timeOf h-t) \<Turnstile> Q r \<and> timeOf h\<ge>t \<and>
     relH {a . a < lim (heapOf h) \<and> a \<notin> (addrOf h)} (heapOf h) (the \<sigma>) \<and>
     lim (heapOf h) \<le> lim (the \<sigma>)))" by auto2

definition run_gen :: "'a Heap \<Rightarrow> heap option \<Rightarrow> heap option \<Rightarrow> 'a \<Rightarrow> bool" where [rewrite]:
  "run_gen c h h' r \<longleftrightarrow> (\<exists>t. run c h h' r t)"

lemma run_genI [forward]: "run c h h' r t \<Longrightarrow> run_gen c h h' r" by auto2

lemma hoare_tripleE':
  "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> run_gen c (Some (heapOf h)) \<sigma> r \<Longrightarrow>
   \<exists>h'. h' \<Turnstile> Q r * Ru \<and> \<sigma> = Some (heapOf h') \<and> success_run c h h' r "
@proof @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @qed

lemma hoare_tripleI:
  "\<not><P> c <Q> \<Longrightarrow> \<exists>h \<sigma> r. h \<Turnstile> P \<and> run_gen c (Some (heapOf h)) \<sigma> r \<and>
   (\<forall>h'. \<sigma> = Some (heapOf h') \<and> success_run c h h' r \<longrightarrow> \<not> h' \<Turnstile> Q r)" by auto2

lemma hoare_triple_mp:
  "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> success_run c h h' r \<Longrightarrow> h' \<Turnstile> (Q r) * Ru"
@proof @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @qed

lemma hoare_tripleE'':
  "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> run_gen (c \<bind> g) (Some (heapOf h)) \<sigma> r \<Longrightarrow>
   \<exists>r' h'. run_gen (g r') (Some (heapOf h')) \<sigma> r \<and> h' \<Turnstile> Q r' * Ru \<and> success_run c h h' r'"
@proof
  @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @then
  @obtain \<sigma>' r' t' where "run c (Some (heapOf h)) \<sigma>' r' t'"
@qed

setup {* del_prfstep_thm @{thm success_run.simps} *}
setup {* del_prfstep_thm @{thm hoare_triple_def} *}
setup {* del_prfstep_thm @{thm hoare_triple_def'} *}
setup {* fold del_prfstep_thm [@{thm pheap.collapse}, @{thm pheap.simps(1)}] *}
setup {* fold del_prfstep_thm @{thms pheap.sel} *}

subsection {* Definition of procedures *}

(* ASCII abbreviations for ML files. *)
abbreviation (input) ex_assn_ascii :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "EXA" 11)
  where "ex_assn_ascii \<equiv> ex_assn"

abbreviation (input) models_ascii :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "|=" 50)
  where "h |= P \<equiv> h \<Turnstile> P"

lemma use_vardef_pair:
  "(\<forall>a b. (a, b) = x \<longrightarrow> P a b) \<longleftrightarrow> P (fst x) (snd x)" by auto

ML_file "../../auto2/HOL/SepLogic/sep_util.ML"
ML_file "rings.ML"
ML_file "rings_test.ML"
ML_file "sep_time_util.ML"
ML_file "assn_time_norm.ML"
ML_file "../../auto2/HOL/SepLogic/assn_matcher.ML"
ML_file "../../auto2/HOL/SepLogic/sep_steps.ML"
ML_file "../../auto2/HOL/SepLogic/sep_steps_test.ML"
ML_file "sep_time_steps.ML"
ML_file "sep_time_test.ML"

attribute_setup sep_proc = {* setup_attrib add_proc_def *}
attribute_setup forward_ent = {* setup_attrib add_forward_ent_prfstep *}
attribute_setup forward_ent_shadow = {* setup_attrib add_forward_ent_shadowing_prfstep *}
attribute_setup rewrite_ent = {* setup_attrib add_rewrite_ent_rule *}
attribute_setup hoare_triple = {* setup_attrib add_hoare_triple_prfstep *}

setup {* fold add_hoare_triple_prfstep [
  @{thm assert_rule}, @{thm update_rule}, @{thm nth_rule}, @{thm upd_rule},
  @{thm return_rule}, @{thm ref_rule}, @{thm lookup_rule}, @{thm new_rule},
  @{thm of_list_rule}, @{thm length_rule}, @{thm freeze_rule}] *}

(* Some simple tests *)

theorem "<$1> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $1> ref x <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $1> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * $1> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * $1> (!b) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $2> do { a := y; !a } <\<lambda>r. a \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $3> do { a := y; a := z; !a } <\<lambda>r. a \<mapsto>\<^sub>r z * \<up>(r = z)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * $2> do { y \<leftarrow> !a; ref y} <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<$1> return x <\<lambda>r. \<up>(r = x)>" by auto2

end
