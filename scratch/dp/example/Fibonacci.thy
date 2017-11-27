theory Fibonacci
  imports "../DP_Lifting" "../DP_CRelVS" "../DP_Proof"
begin
  
  (*
fun fib :: "nat \<Rightarrow> int option" where
  "fib 0 = Some 0"
| "fib (Suc 0) = Some 1"
| "fib (Suc (Suc n)) = (case (fib (Suc n), fib n) of (Some f1, Some f0) \<Rightarrow> Some (f1 + f0) | _ \<Rightarrow> None)"
term 0 (**)
*)

fun fib :: "nat \<Rightarrow> int option" where
  "fib 0 = Some 0"
| "fib (Suc 0) = Some 1"
| "fib (Suc (Suc n)) = case_prod
      (\<lambda>of1 of0. case_option
        None
        (\<lambda>f1. case_option
          None
          (\<lambda>f0. Some (f1 + f0))
          of0)
        of1)
      (Pair (fib (Suc n)) (fib n))"

ML_file \<open>../Transform.ML\<close>
local_setup \<open>
lift_fun NONE;
\<close>

interpretation fib: dp_consistency fib .

lemma fib\<^sub>T_correct:
  "fib.consistentDP fib\<^sub>T"
  by (dp_match induct: fib\<^sub>T.induct simp: fib.simps simp\<^sub>T: fib\<^sub>T.simps)

definition fib\<^sub>T_entry :: "nat \<Rightarrow> int option" where
  "fib\<^sub>T_entry n \<equiv> fst (runState (fib\<^sub>T n) Mapping.empty)"

lemma fib\<^sub>T_entry_correct:
  "fib\<^sub>T_entry = fib"
  unfolding fib\<^sub>T_entry_def using fib.consistentDP_entry[OF fib\<^sub>T_correct] ..

lemma Let_absorb:
  "(let (a, b) = (let (c, d) = x in (p c d, q c d)) in f a b)
 = (let (c, d) = x; (a, b) = (p c d, q c d) in f a b)"
  by (auto simp: Let_def split: prod.splits)

lemma Let_absorb2:
  "(let (a, b) = (let (c, d) = x; (e, f) = y c d in (p c d e f, q c d e f)) in g a b)
 = (let (c, d) = x; (e, f) = y c d; (a, b) = (p c d e f, q c d e f) in g a b)"
  by (auto simp: Let_def split: prod.splits)

lemma Let_unfold_pair:
  "(let (a, b) = (x, y) in f a b) = f x y"
  by (auto simp: Let_def split: prod.splits)

lemma Let_split_pair:
  "(let (a, b) = (x, y) in f a b) = (let a=x; b=y in f a b)"
  by auto

lemma runState_option:
  "runState (case x of None \<Rightarrow> f0 | Some y \<Rightarrow> ifSome f1 y) M
 = (case x of None \<Rightarrow> runState f0 M | Some y \<Rightarrow> runState (ifSome f1 y) M)"
  by (auto split: option.split)


definition "runState' \<equiv> runState"


schematic_goal fib\<^sub>T_simp1:
  "runState (fib\<^sub>T 0) M = ?x"
  apply (subst fib\<^sub>T.simps(1))
  apply (subst checkmem_def)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst get_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst bind_def)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst bind_def)
  apply (subst get_def)
  apply (subst state.sel)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst bind_def)
  apply (subst put_def)
  apply (subst state.sel)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst runState_option)
  apply (subst state.sel)
  apply (subst return_def)
  apply (subst state.sel)
  apply (rule refl)
  done

schematic_goal fib\<^sub>T_simp2:
  "runState (fib\<^sub>T (Suc 0)) M = ?x"
  apply (subst fib\<^sub>T.simps(2))
  apply (subst checkmem_def)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst get_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst bind_def)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst bind_def)
  apply (subst get_def)
  apply (subst state.sel)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst bind_def)
  apply (subst put_def)
  apply (subst state.sel)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst runState_option)
  apply (subst state.sel)
  apply (subst return_def)
  apply (subst state.sel)
  apply (rule refl)
  done

schematic_goal fib\<^sub>T_simp3:
  "runState (fib\<^sub>T (Suc (Suc n))) M = ?x"
  apply (subst fib\<^sub>T.simps(3))
  apply (subst checkmem_def)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst get_def)
  apply (subst state.sel)
  apply (subst Let_def)
  apply (subst prod.case)
  apply (subst fun_app_lifted_def)
  apply (subst bind_def)
  apply (subst case_prod\<^sub>T_def)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_def)
  apply (subst prod.case)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_def)
  apply (subst prod.case)
  apply (subst unlift_33_def)
  apply (subst fun_app_lifted_def)
  apply (subst bind_def)
  apply (subst return_def)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst state.sel)
  apply (subst return_def)
  apply (subst Let_unfold_pair)
  apply (subst state.collapse)
  apply (subst bind_def)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst state.sel)
  apply (subst bind_def)
  apply (subst fun_app_lifted_def)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst state.collapse)
  apply (subst fun_app_lifted_def)
  apply (subst bind_def)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst state.collapse)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst fun_app_lifted_def)
  apply (subst bind_def)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst state.collapse)
  apply (subst fun_app_lifted_def)
  apply (subst bind_def)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_absorb)
  apply (subst Let_unfold_pair)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst state.sel)
  apply (subst Let_absorb2)
  apply (subst Let_unfold_pair)
  apply (subst prod.case)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst Let_absorb2)
  apply (subst Let_split_pair)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst bind_def)
  apply (subst state.sel)
  apply (subst put_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst get_def)
  apply (subst state.sel)
  apply (subst Let_unfold_pair)
  apply (subst return_def)
  apply (subst state.sel)
  apply (subst runState_option)
  apply (subst state.sel)
  apply (subst return_def)
  apply (subst state.sel)
  apply (unfold runState'_def[symmetric])
  apply (rule refl)
  done

lemmas fib\<^sub>T_runState_simps[code_unfold] =
  fib\<^sub>T_simp1 fib\<^sub>T_simp2 fib\<^sub>T_simp3

fun fib\<^sub>T' :: "nat \<Rightarrow> (nat, int option) mapping \<Rightarrow> (int option \<times> (nat, int option) mapping)" where
  "fib\<^sub>T' 0 M = runState (fib\<^sub>T 0) M"
| "fib\<^sub>T' (Suc 0) M = runState (fib\<^sub>T (Suc 0)) M"
| "fib\<^sub>T' (Suc (Suc n)) M = runState (fib\<^sub>T (Suc (Suc n))) M"

lemma runState'_fold[code_unfold]:
  "runState' (fib\<^sub>T n) M = fib\<^sub>T' n M"
  unfolding runState'_def by (induction rule: fib\<^sub>T'.induct) auto

definition fib\<^sub>T'_entry where
  "fib\<^sub>T'_entry n \<equiv> fst (fib\<^sub>T' n Mapping.empty)"

lemma fib\<^sub>T'_entry_correct:
  "fib\<^sub>T'_entry = fib"
  apply (unfold fib\<^sub>T_entry_correct[symmetric])
  unfolding fib\<^sub>T'_entry_def fib\<^sub>T_entry_def
  apply (rule ext)
  apply (rule arg_cong[where f=fst])
  apply (induct_tac rule: fib\<^sub>T'.induct)
    apply auto
  done

export_code fib\<^sub>T'_entry in SML

end