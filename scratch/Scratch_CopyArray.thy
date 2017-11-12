theory Scratch_CopyArray
  imports Refine_Imperative_HOL.IICF
begin

definition fill_one_spec :: "int list \<Rightarrow> int list nres" where
  "fill_one_spec l \<equiv> RETURN (map (\<lambda>_. 1) l)"

definition fill_one1 :: "int list \<Rightarrow> int list nres" where
  "fill_one1 l \<equiv> RETURN (fold (\<lambda>i l. (list_update l i 1)) [0..<length l] l)"

lemma fold_fix_length: "x \<le> length l \<Longrightarrow> length (fold (\<lambda>i l. (list_update l i 1)) [0..<x] l) = length l"
  by (induction x) auto

lemma fill_replicate_partial: "x \<le> length l \<Longrightarrow> take x (fold (\<lambda>i l. (list_update l i 1)) [0..<x] l) = replicate x 1" for x
  by (induction x) (auto simp: take_update_last replicate_append_same fold_fix_length)

corollary fill_replicate: "fold (\<lambda>i l. (list_update l i 1)) [0..<length l] l = replicate (length l) 1"
  using fill_replicate_partial by (fastforce simp: fold_fix_length)

corollary fill_length_cong:
  assumes "length l0 = length l1"
  shows "fold (\<lambda>i l. (list_update l i 1)) [0..<length l0] l1 = replicate (length l1) 1"
  unfolding assms fill_replicate ..

lemma fill_one1_refine: "(fill_one1, fill_one_spec) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding fill_one_spec_def fill_one1_def
  apply (refine_vcg)
  apply (vc_solve simp: fill_replicate map_replicate_const)
  done

definition fill_one2 :: "int list \<Rightarrow> int list nres" where
  "fill_one2 l \<equiv> nfoldli [0..<length l] (\<lambda>_. True) (\<lambda>i l'. ASSERT (i < length l') \<then> RETURN (list_update l' i 1)) l"

lemma fill_one2_refine: "(fill_one2, fill_one1) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding fill_one2_def fill_one1_def
  apply (refine_vcg nfoldli_rule[where I="\<lambda>l1 l2 l. take (length l1) l = replicate (length l1) 1 \<and> length l1 + length l2 = length l"])
        apply (vc_solve simp: upt_eq_lel_conv take_update_last replicate_append_same fill_length_cong)
  done

sepref_definition fill_one3 is fill_one2 :: "(array_assn int_assn)\<^sup>d \<rightarrow>\<^sub>a (array_assn int_assn)"
  unfolding fill_one2_def
  by sepref


lemmas fill_one3_correct = fill_one3.refine[FCOMP fill_one2_refine, FCOMP fill_one1_refine]

lemma fill_one2_refine': "(fill_one2, fill_one_spec) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding fill_one2_def fill_one_spec_def
  apply (refine_vcg nfoldli_rule[where I="\<lambda>l1 l2 l. l = map (\<lambda>_. 1) (take (length l1) l) @ drop (length l1) l \<and> length l = length l1 + length l2"])
        apply (vc_solve simp: upt_eq_lel_conv replicate_append_same[symmetric] map_replicate_const upd_conv_take_nth_drop)
  subgoal premises prems
    apply (rewrite prems(1))
    apply simp
    done
  done

end