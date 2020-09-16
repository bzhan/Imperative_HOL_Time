theory IHT_Matrix
  imports 
    SLTC_Main Asymptotics_2D
begin

section \<open>Some lemmas about indexing\<close>

lemma matrix_id_less [backward]: "(i::nat) < m \<Longrightarrow> j < n \<Longrightarrow> i * n + j < m * n"
@proof
  @have "i \<le> m - 1"
  @have "i * n \<le> (m - 1) * n"
  @have "i * n + j < (m - 1) * n + n"
@qed

lemma matrix_id_inj [forward]:
  "i * n + j = i' * n + j' \<Longrightarrow> (j::nat) < n \<Longrightarrow> j' < n \<Longrightarrow> i = i' \<and> j = j'"
  by (smt Suc_leI add.commute add_scale_eq_noteq div_eq_0_iff div_mult_mod_eq le_0_eq mod_mult_self3 mult.commute nat.simps(3))

section \<open>Abstract matrix as a list of lists\<close>

definition empty_matrix :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where [rewrite]:
  "empty_matrix m n x = replicate m (replicate n x)"

definition mat_update :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where [rewrite]:
  "mat_update M i j x = list_update M i (list_update (M ! i) j x)"

section \<open>Implementation of a matrix\<close>

datatype 'a matrix = Matrix (nrow: nat) (ncol: nat) (aref: "'a array")
setup \<open>add_simple_datatype "matrix"\<close>

(* m is number of rows, n is number of columns *)
definition init_matrix :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a::heap matrix Heap" where
  "init_matrix m n x = do {
     a \<leftarrow> Array_Time.new (m * n) x;
     return (Matrix m n a)
   }"

(* i is row index, j is column index *)
fun nth_matrix :: "nat \<Rightarrow> nat \<Rightarrow> 'a::heap matrix \<Rightarrow> 'a Heap" where
  "nth_matrix i j p = (case p of (Matrix m n a) \<Rightarrow>
     Array_Time.nth a (i * n + j))"

(* i is row index, j is column index, x is new value *)
fun upd_matrix :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a::heap matrix \<Rightarrow> unit Heap" where
  "upd_matrix i j x p = (case p of (Matrix m n a) \<Rightarrow>
     do {Array_Time.upd (i * n + j) x a; return ()})"

definition matrix_rel :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where [rewrite]:
  "matrix_rel xs m n as \<longleftrightarrow> (length as = m * n \<and> length xs = m \<and> (\<forall>i<m. length (xs ! i) = n) \<and> (\<forall>i<m. \<forall>j<n. (xs ! i) ! j = as ! (i * n + j)))"

fun matrix_assn :: "nat \<Rightarrow> 'a::heap list list \<Rightarrow> 'a matrix \<Rightarrow> assn" where
  "matrix_assn nc xs (Matrix m n a) = (\<exists>\<^sub>Aas. a \<mapsto>\<^sub>a as * \<up>(matrix_rel xs m n as) * \<up>(n = nc))"
setup \<open>add_rewrite_ent_rule @{thm matrix_assn.simps}\<close>

lemma matrix_rel_empty [resolve]:
  "matrix_rel (empty_matrix m n x) m n (replicate (m * n) x)"
@proof
  @have "\<forall>i<m. \<forall>j<n. empty_matrix m n x ! i ! j = replicate (m * n) x ! (i * n + j)" @with
    @have "i * n + j < m * n"
  @end
@qed

lemma matrix_rel_nth [rewrite]:
  "matrix_rel xs m n as \<Longrightarrow> i < m \<Longrightarrow> j < n \<Longrightarrow> as ! (i * n + j) = xs ! i ! j" by auto2

fun init_matrix_time :: "nat * nat \<Rightarrow> nat" where  
  "init_matrix_time (m,n) = m * n + 2"
declare init_matrix_time.simps [rewrite]

lemma init_matrix_correct [hoare_triple]:
  "<$(init_matrix_time (m, n))>
   init_matrix m n x
   <matrix_assn n (empty_matrix m n x)>" by auto2

lemma init_matrix_time_bound [asym_bound]: "init_matrix_time \<in> \<Theta>\<^sub>2(\<lambda>x. real (fst x * snd x))"
  apply (subst surjective_pairing) unfolding init_matrix_time.simps by auto2

lemma nth_matrix_correct [hoare_triple]:
  "i < length xs \<Longrightarrow> j < n \<Longrightarrow>
   <matrix_assn n xs p * $1>
    nth_matrix i j p
   <\<lambda>r. matrix_assn n xs p * \<up>(r = xs ! i ! j)>" by auto2

lemma upd_matrix_correct [hoare_triple]:
  "i < length xs \<Longrightarrow> j < n \<Longrightarrow>
   <matrix_assn n xs p * $2>
    upd_matrix i j x p
   <\<lambda>_. matrix_assn n (mat_update xs i j x) p>" by auto2

setup \<open>del_prfstep_thm @{thm matrix_assn.simps}\<close>

end
