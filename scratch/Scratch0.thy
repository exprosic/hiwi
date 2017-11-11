theory Scratch0
  imports Refine_Imperative_HOL.IICF
begin

fun fib :: "nat \<Rightarrow> int" where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib (Suc n) + fib n"

definition fib_imp :: "nat \<Rightarrow> int nres" where
  "fib_imp n \<equiv> SPEC (op = (fib n))"

term WHILEIT
term WHILET
definition fib_imp0 :: "nat \<Rightarrow> int nres" where
  "fib_imp0 n \<equiv> do {
    (_, x, _) \<leftarrow> WHILEIT
      (\<lambda>(i, f0, f1). i\<le>n \<and> f0 = fib i \<and> f1 = fib (Suc i))
      (\<lambda>(i, f0, f1). i < n)
      (\<lambda>(i, f0, f1). RETURN (Suc i, f1, f0+f1))
      (0, 1, 1);
    RETURN x
  }"

term nat_assn
term Id

lemma "(fib_imp0, fib_imp) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
proof -
  have "fib_imp0 n \<le> fib_imp n" for n
  proof -
    have fib_measure: "wf (measure (\<lambda>(i, f0, f1). n-i))"
      by simp
    show ?thesis
      unfolding fib_imp_def fib_imp0_def
      by (refine_vcg fib_measure) auto
  qed
  thus ?thesis
    by (clarsimp intro!: nres_relI)
qed

term while
term last

definition fib_imp' :: "nat \<Rightarrow> int list nres" where
  "fib_imp' n \<equiv> SPEC (op = [fib i. i \<leftarrow> [0..<n]])"

definition fib_imp0':: "nat \<Rightarrow> int list nres" where
  "fib_imp0' n \<equiv> RETURN (take n (fold (\<lambda>i l. l@[(l!i) + (l!(Suc i))]) [0..<n] [1, 1]))"

lemma "(fib_imp0', fib_imp') \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
proof -
  have "fib_imp0' n \<le> fib_imp' n" for n
  proof -
    have fib_fold: "fold (\<lambda>i l. l@[(l!i) + (l!(Suc i))]) [0..<m] [1, 1] = map fib [0..<m+2]" for m
      by (induction m) (auto simp: nth_append)
    show ?thesis
      unfolding fib_imp'_def fib_imp0'_def
      by (refine_vcg) (auto simp: fib_fold)
  qed
  thus ?thesis
    by (clarsimp intro!: nres_relI)
qed

sepref_definition fib_imp1' is fib_imp0' :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a (list_assn int_assn)"
  unfolding fib_imp0'_def
unfolding "HOL_list.fold_custom_empty"
  apply sepref_dbg_preproc
  -- \<open>The next phase applies a consequence rule for the postcondition and
    result. This is mainly for technical reasons.\<close>
  apply sepref_dbg_cons_init
  -- \<open>The next phase tries to identify the abstract operations, and inserts
    tag-constants for function application and abstraction. These tags are for 
    technical reasons, working around Isabelle/HOL's unifier idiosyncrasies.

    Operation identification assigns a single constant to each abstract operation,
    which is required for technical reasons. Note that there are terms in HOL, 
    which qualify as a single operation, but consists of multiple constants, 
    for example, @{term "{x}"}, which is just syntactic sugar for 
    @{term [source] "insert x {}"}. In our case, the operation identification 
    phase rewrites the assertion operations followed by a bind to a single 
    operation @{const op_ASSERT_bind}, and renames some operations to more 
    canonical names.
    \<close>
  apply sepref_dbg_id
  -- \<open>Now that it is clear which operations to execute, we have to specify an 
    execution order. Note that HOL has no notion of execution at all. However,
    if we want to translate to operations that depend on a heap, we need a notion 
    of execution order. We use the \<open>nres\<close>-monad's bind operation as sequencing operator,
    and flatten all nested operations, using left-to-right evaluation order. 
    \<close>
  apply sepref_dbg_monadify
  -- \<open>The next step just prepares the optimization phase,
    which will be executed on the translated program. It just applies the rule   
    @{thm TRANS_init}.\<close>
  apply sepref_dbg_opt_init
  -- \<open>The translation phase does the main job of translating the abstract program
    to the concrete one. It has rules how to translate abstract operations to
    concrete ones. For technical reasons, it differentiates between 
    operations, which have only first-order arguments (e.g., @{const length})   
    and combinators, which have also higher-order arguments (e.g., @{const fold}).

    The basic idea of translation is to repeatedly apply the translation rule for the
    topmost combinator/operator, and thus recursively translate the whole program.
    The rules may produce various types of side-conditions, which are resolved by the tool.
    \<close>
      apply sepref_dbg_trans_step
        apply sepref_dbg_trans_step

          apply sepref_dbg_trans_step
            apply sepref_dbg_trans_step
           apply sepref_dbg_trans_step
          apply sepref_dbg_trans_step

         apply sepref_dbg_trans_step
           apply sepref_dbg_trans_step
             apply sepref_dbg_trans_step
            apply sepref_dbg_trans_step
              apply sepref_dbg_trans_step
                apply sepref_dbg_trans_step
             apply sepref_dbg_trans_step
               apply sepref_dbg_trans_step
              apply sepref_dbg_trans_step
             apply sepref_dbg_trans_step
            apply sepref_dbg_trans_step
           apply sepref_dbg_trans_step
          apply sepref_dbg_trans_step
         apply sepref_dbg_trans_step
        apply sepref_dbg_trans_step
               apply sepref_dbg_trans_step
              apply sepref_dbg_trans_step
             apply sepref_dbg_trans_step
            apply sepref_dbg_trans_step
           apply sepref_dbg_trans_step
          apply sepref_dbg_trans_step
            apply sepref_dbg_trans_step
              apply sepref_dbg_trans_step
apply sepref_dbg_trans_step_keep


  
  term 0(*
  find_theorems op_list_get hn_refine
  term list_custom_empty
  thm HOL_list.fold_custom_empty
  thm op_list_prepend_def[symmetric]
  thm op_list_get_def
end