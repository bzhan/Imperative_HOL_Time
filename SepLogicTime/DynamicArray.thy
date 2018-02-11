theory DynamicArray
  imports SepAuto Arrays_Impl
begin

datatype 'a dynamic_array = Dyn_Array (alen: nat) (aref: "'a array")
setup {* add_rewrite_rule_back @{thm dynamic_array.collapse} *}
setup {* add_rewrite_rule @{thm dynamic_array.case} *}
setup {* fold add_rewrite_rule @{thms dynamic_array.sel} *}

section {* Raw assertion and basic operations *}

fun dyn_array_raw :: "'a::heap list \<times> nat \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where
  "dyn_array_raw (xs, n) (Dyn_Array m a) = (a \<mapsto>\<^sub>a xs * \<up>(m = n))"
setup {* add_rewrite_ent_rule @{thm dyn_array_raw.simps} *}

definition dyn_array_new :: "'a::heap dynamic_array Heap" where [sep_proc]:
  "dyn_array_new = do {
     p \<leftarrow> Array.new 5 undefined;
     return (Dyn_Array 0 p)
   }"

lemma dyn_array_new_raw_rule [hoare_triple]:
  "<$7>
   dyn_array_new
   <dyn_array_raw (replicate 5 undefined, 0)>" by auto2

definition double_length :: "'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where [sep_proc]:
  "double_length d = (case d of Dyn_Array al ar \<Rightarrow> do {
      am \<leftarrow> Array.len ar;
      p \<leftarrow> Array.new (2 * am + 1) undefined;
      array_copy ar p am;
      return (Dyn_Array am p)
    })"

fun double_length_fun :: "'a::heap list \<times> nat \<Rightarrow> 'a list \<times> nat" where
  "double_length_fun (xs, n) =
    (Arrays_Ex.array_copy xs (replicate (2 * n + 1) undefined) n, n)"
setup {* add_rewrite_rule @{thm double_length_fun.simps} *}

lemma double_length_raw_rule [hoare_triple]:
  "length xs = n \<Longrightarrow>
   <dyn_array_raw (xs, n) p * $(5*n + 5)>
   double_length p
   <dyn_array_raw (double_length_fun (xs, n))>\<^sub>t" by auto2

definition push_array_basic :: "'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where [sep_proc]:
  "push_array_basic x p = do {
    Array.upd (alen p) x (aref p);
    return (Dyn_Array (alen p + 1) (aref p))
   }"

fun push_array_basic_fun :: "'a \<Rightarrow> 'a::heap list \<times> nat \<Rightarrow> 'a list \<times> nat" where
  "push_array_basic_fun x (xs, n) = (list_update xs n x, n + 1)"
setup {* add_rewrite_rule @{thm push_array_basic_fun.simps} *}

lemma push_array_basic_raw_rule [hoare_triple]:
  "n < length xs \<Longrightarrow>
   <dyn_array_raw (xs, n) p * $2>
    push_array_basic x p
   <dyn_array_raw (push_array_basic_fun x (xs, n))>" by auto2

section {* Potential function *}

lemma arith1 [rewrite]: "10*(n::nat) - 5*(2*n+1) = 0" by simp
lemma arith2 [backward]: "a \<le> b \<Longrightarrow> c > 0 \<Longrightarrow> a + c - b \<le> (c::nat)" by auto

lemma arith2' [resolve]: "10*(a::nat) - 5*b + 12 \<ge> 10*(a+1) - 5*b + 2"
@proof
  @case "10*a \<ge> 5*b"
  @have "10*a - 5*b + 12 = 12" @with  (* lhs *)
    @have "10*a - 5*b = 0"
  @end
  @case "10*(a+1) < 5*b"
  @have "10*a + 10 \<ge> 5 * b"
  @have "10*(a+1) - 5*b + 2 = 10*a + 12 - 5*b"
@qed

fun dyn_array_P :: "'a::heap list \<times> nat \<Rightarrow> nat" where
  "dyn_array_P (xs, n) = 10 * n - 5 * length xs"
setup {* add_rewrite_rule @{thm dyn_array_P.simps} *}

lemma dyn_array_new_P [rewrite]:
  "dyn_array_P (replicate 5 undefined, 0) = 0" by auto2

lemma double_length_fun_P [resolve]:
  "length xs = n \<Longrightarrow>
   dyn_array_P (xs, n) + 4 \<ge> dyn_array_P (double_length_fun (xs, n)) + (5*n+4)" by auto2

lemma push_array_fun_P [resolve]:
  "n \<le> length xs \<Longrightarrow>
   dyn_array_P (xs, n) + 12 \<ge> dyn_array_P (push_array_basic_fun x (xs, n)) + 2" by auto2

lemma update_P [rewrite]:
  "i < n \<Longrightarrow> dyn_array_P (list_update xs i x, n) = dyn_array_P (xs, n)" by auto2

setup {* del_prfstep_thm @{thm dyn_array_P.simps} *}

section {* Refined assertion *}

definition dyn_array' :: "'a::heap list \<times> nat \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where [rewrite_ent]:
  "dyn_array' p r = dyn_array_raw p r * $(dyn_array_P p)"

lemma dyn_array_new_rule' [hoare_triple]:
  "<$7>
   dyn_array_new
   <dyn_array' (replicate 5 undefined, 0)>\<^sub>t"
@proof
  @have "7 \<ge>\<^sub>t 7 + dyn_array_P (replicate 5 undefined, 0)"
@qed

lemma double_length_rule' [hoare_triple]:
  "length xs = n \<Longrightarrow>
   <dyn_array' (xs, n) p * $5>
   double_length p
   <dyn_array' (double_length_fun (xs, n))>\<^sub>t"
@proof
  @have "dyn_array_P (xs, n) + 4 \<ge>\<^sub>t dyn_array_P (double_length_fun (xs, n)) + (5*n+4)"
@qed

lemma push_array_basic_rule' [hoare_triple]:
  "n < length xs \<Longrightarrow>
   <dyn_array' (xs, n) p * $12>
    push_array_basic x p 
   <dyn_array' (list_update xs n x, n + 1)>\<^sub>t"
@proof
  @have "dyn_array_P (xs, n) + 12 \<ge>\<^sub>t dyn_array_P (push_array_basic_fun x (xs, n)) + 2"
@qed

definition array_length :: "'a::heap dynamic_array \<Rightarrow> nat Heap" where [sep_proc]:
  "array_length d = return (alen d)"

lemma array_length_rule' [hoare_triple]:
  "<dyn_array' (xs, n) p * $1>
   array_length p
   <\<lambda>r. dyn_array' (xs, n) p * \<up>(r = n)>" by auto2

definition array_max :: "'a::heap dynamic_array \<Rightarrow> nat Heap" where [sep_proc]:
  "array_max d = Array.len (aref d)"

lemma array_max_rule' [hoare_triple]:
  "<dyn_array' (xs, n) p * $1>
   array_max p
   <\<lambda>r. dyn_array' (xs, n) p * \<up>(r = length xs)>" by auto2

definition array_nth :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> 'a Heap" where [sep_proc]:
  "array_nth d i = Array.nth (aref d) i"

lemma array_nth_rule' [hoare_triple]:
  "i < n \<Longrightarrow> n \<le> length xs \<Longrightarrow>
   <dyn_array' (xs, n) p * $1>
   array_nth p i
   <\<lambda>r. dyn_array' (xs, n) p * \<up>(r = xs ! i)>" by auto2

definition array_upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> unit Heap" where [sep_proc]:
  "array_upd i x d = do { Array.upd i x (aref d); return () }"

lemma array_upd_rule' [hoare_triple]:
  "i < n \<Longrightarrow> n \<le> length xs \<Longrightarrow>
   <dyn_array' (xs, n) p * $2>
   array_upd i x p
   <\<lambda>_. dyn_array' (list_update xs i x, n) p>" by auto2

section {* Derived operations *}

definition push_array :: "'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where [sep_proc]:
  "push_array x p = do {
    m \<leftarrow> array_max p;
    l \<leftarrow> array_length p;
    if l < m then push_array_basic x p
    else do {
      u \<leftarrow> double_length p;
      push_array_basic x u
    }
  }"

fun push_array_fun :: "'a \<Rightarrow> 'a::heap list \<times> nat \<Rightarrow> 'a list \<times> nat" where
  "push_array_fun x (xs, n) = (
     if n < length xs then push_array_basic_fun x (xs, n)
     else push_array_basic_fun x (double_length_fun (xs, n)))"
setup {* add_rewrite_rule @{thm push_array_fun.simps} *}

section {* Abstract assertion *}

fun abs_array :: "'a::heap list \<times> nat \<Rightarrow> 'a list" where
  "abs_array (xs, n) = take n xs"
setup {* add_rewrite_rule @{thm abs_array.simps} *}

lemma double_length_abs [rewrite]:
  "length xs = n \<Longrightarrow> abs_array (double_length_fun (xs, n)) = abs_array (xs, n)" by auto2

lemma push_array_basic_abs [rewrite]:
  "n < length xs \<Longrightarrow> abs_array (push_array_basic_fun x (xs, n)) = abs_array (xs, n) @ [x]"
@proof @have "length (take n xs @ [x]) = n + 1" @qed

lemma push_array_fun_abs [rewrite]:
  "n \<le> length xs \<Longrightarrow> abs_array (push_array_fun x (xs, n)) = abs_array (xs, n) @ [x]" by auto2

end
