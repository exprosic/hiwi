theory Scratch_Wfrec
  imports Main "HOL-Library.Old_Recdef" "dp/DP_CrelVS" Rewrite
begin

consts fib :: "nat \<Rightarrow> int"
recdef fib "measure id"
  "fib 0 = 1"
  "fib (Suc 0) = 1"
  "fib (Suc (Suc n)) = plus (fib (Suc n)) (fib n)"
print_theorems

consts fibT :: "nat \<Rightarrow>\<^sub>T int"
recdef fibT "measure id"
  "fibT$ 0 =CHECKMEM= \<langle>1\<rangle>"
  "fibT$ (Suc 0) =CHECKMEM= \<langle>1\<rangle>"
  "fibT$ (Suc (Suc n)) =CHECKMEM= plus\<^sub>T . (fibT (Suc n)) . (fibT n)"

print_theorems
thm wfrec_fixpoint

context dp_consistency
begin
context includes lifting_syntax
begin
lemma
  assumes "wf wfR"
  assumes "adm_wf wfR body"
  assumes "adm_wf wfR bodyT"
  assumes "((op = ===>\<^sub>T op =) ===> (op = ===>\<^sub>T op =)) (body) (bodyT)"
  shows "(op = ===>\<^sub>T op =) (wfrec wfR body) (wfrec wfR bodyT)"
proof -
  show ?thesis
    apply (rule rel_funI)
    apply clarsimp
    subgoal for x
      using assms(1) apply (induction x rule: wf_induct_rule)
      subgoal premises IH for x 
        thm IH
        apply (rewrite in "_ body" wfrec_fixpoint)
        subgoal using assms(1) .
        subgoal using assms(2) .
        apply (rewrite in "_ bodyT" wfrec_fixpoint)
        subgoal using assms(1) .
        subgoal using assms(3) .
        using IH assms(4)[THEN rel_funD, OF rel_funI, THEN rel_funD
            , where x1="wfrec wfR body" and y1="wfrec wfR bodyT" and x=x and y=x
            , simplified
            ]
        ML_val \<open>@{method rewrite}\<close>
end
end