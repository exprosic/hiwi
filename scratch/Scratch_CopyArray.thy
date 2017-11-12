theory Scratch_CopyArray
  imports Refine_Imperative_HOL.IICF
begin

definition fill_one :: "int list \<Rightarrow> int list nres" where
  "fill_one l \<equiv> RETURN (map (\<lambda>_. 1) l)"

definition fill_one1 :: "int list \<Rightarrow> int list nres" where
  "fill_one1 l \<equiv> RETURN (fold (\<lambda>i l. (list_update l i 1)) [0..<length l] l)"

lemma "(fill_one1, fill_one) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
proof -
  { fix l :: "int list"
    have fix_len[simp]: "x \<le> length l \<Longrightarrow> length (fold (\<lambda>i l. (list_update l i 1)) [0..<x] l) = length l" for x
      by (induction x) auto
    have "x \<le> length l \<Longrightarrow> take x (fold (\<lambda>i l. (list_update l i 1)) [0..<x] l) = replicate x 1" for x
      by (induction x) (auto simp: take_update_last replicate_append_same)
    note this[of "length l", simplified, folded map_replicate_const]
  }
  thus ?thesis
    unfolding fill_one_def fill_one1_def
    by refine_vcg auto
qed

sepref_definition fill_one2 is fill_one1 :: "(array_assn int_assn)\<^sup>d \<rightarrow>\<^sub>a (array_assn int_assn)"
  unfolding fill_one1_def
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
          apply sepref_dbg_trans_step_keep
  apply (sepref_dbg_side_keep)
  term 0(*          apply sepref_dbg_trans_step_keep
         apply sepref_dbg_trans_step_keep
           apply sepref_dbg_trans_step_keep
          apply sepref_dbg_trans_step_keep
         apply sepref_dbg_trans_step_keep
        apply sepref_dbg_trans_step_keep
       apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
           apply sepref_dbg_trans_step_keep
          apply sepref_dbg_trans_step_keep
         apply sepref_dbg_trans_step_keep
           apply sepref_dbg_trans_step_keep
          apply sepref_dbg_trans_step_keep
          apply sepref_dbg_trans_step_keep
          apply sepref_dbg_trans_step_keep
  
end