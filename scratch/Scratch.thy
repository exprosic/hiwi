theory Scratch
  imports Refine_Imperative_HOL.IICF
begin
      
lemma "(if b then fx else fy) x = (if b then fx x else fy x)"
  using [[simp_trace]]
  apply auto