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

definition fib_imp0' :: "nat \<Rightarrow> int list nres" where
  "fib_imp0' n = RETURN (take n (fold (\<lambda>i l. (list_update l (i+2) (l!i+l!(i+1)))) [0..<n] (replicate (n+2) 1)))"
term list_update
term Ref.update

lemma "(fib_imp0', fib_imp') \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
proof -
  have "fib_imp0' n \<le> fib_imp' n" for n
  proof -
    have fib_fold: "take m (fold (\<lambda>i l. (list_update l (i+2) (l!i+l!(i+1)))) [0..<m] (replicate (m+2) 1)) = map fib [0..<m]" for m
      apply (induction m)
       apply auto[]
      find_theorems imp_for
      term while
      oops
      term replicate

sepref_definition fib_imp1' is fib_imp0' :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a (list_assn int_assn)"
  unfolding fib_imp0'_def
unfolding "HOL_list.fold_custom_empty"
      apply sepref_dbg_keep
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
               apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep

  
  term 0(*
  find_theorems op_list_get hn_refine
  term list_custom_empty
  thm HOL_list.fold_custom_empty
  thm op_list_prepend_def[symmetric]
  thm op_list_get_def
end