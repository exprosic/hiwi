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

lemma option_case_distrib2:
  "(case_option f1 f2 x) v = case_option (f1 v) (\<lambda>y. f2 y v) x"
  by (auto split: option.split)
  
lemma prod_absorb:
  "(case (case a of (c, d) \<Rightarrow> (f c d, g c d)) of
  (p, q) \<Rightarrow> h p q) = (case a of (c, d) \<Rightarrow>
  (h (f c d) (g c d)))"
  by (auto split: prod.splits)

thm case_prod_beta
lemma Let_absorb:
  "(let (a, b) = (let (c, d) = x in (p c d, q c d)) in f a b)
 = (let (c, d) = x in f (p c d) (q c d))"
  by (auto simp: Let_def split: prod.splits)

schematic_goal "?x = runState (fib\<^sub>T (Suc (Suc n))) Mapping.empty"
  unfolding fib\<^sub>T.simps
  unfolding case_prod\<^sub>T_def
  unfolding checkmem_def
  unfolding unlift_33_def
  unfolding fun_app_lifted_def
  unfolding return_def
  unfolding bind_def
  unfolding option.case_distrib option_case_distrib2
  unfolding state.sel
  unfolding Let_absorb
  unfolding Let_def
  unfolding state.sel
  unfolding prod.case
  unfolding state.sel
  unfolding prod.case
  unfolding prod_absorb
  unfolding state.sel state.collapse
  unfolding prod.case_distrib option.case_distrib
  unfolding get_def put_def
  unfolding state.sel
  unfolding prod.case
  unfolding prod_absorb
  unfolding option_case_distrib2
  unfolding prod_absorb
  oops

term 0 (*
export_code fib\<^sub>T_entry in SML
end