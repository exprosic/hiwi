theory DP_CRelVS
  imports "./Monad" "./DP_Lifting" "HOL-Library.RBT_Mapping"
begin

locale mem_correct = mem_defs +
  assumes lookup_correct: "\<And>v m'. runState (lookup k) m = (v, m') \<Longrightarrow> mem_map m k = v \<and> mem_map m' = mem_map m"
    and update_correct: "\<And>u m'. runState (update k v) m = (u, m') \<Longrightarrow> mem_map m' = (mem_map m)(k\<mapsto>v)"
    and empty_correct: "mem_map (empty_mem) = Map.empty"

locale dp_consistency =
  mem_correct lookup for lookup :: "'param \<Rightarrow> ('mem, 'result option) state"  +
  fixes dp :: "'param \<Rightarrow> 'result"
begin
  
context
  includes lifting_syntax
begin
  
  (* Predicates *)
definition cmem :: "'mem \<Rightarrow> bool" where
  "cmem M \<equiv> \<forall>param\<in>dom (mem_map M). mem_map M param = Some (dp param)"
term 0 (**)
  
definition crel_vs :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('mem, 'b) state \<Rightarrow> bool" where
  "crel_vs R v s \<equiv> \<forall>M. cmem M \<longrightarrow> (case runState s M of (v', M') \<Rightarrow> R v v' \<and> cmem M')"
  
definition crel_vs_alt :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('mem, 'b) state \<Rightarrow> bool" where
  "crel_vs_alt R v s \<equiv> pred_fun cmem (pred_prod (R v) cmem) (runState s)"

abbreviation rel_fun_lifted :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c ==_\<Longrightarrow> 'd) \<Rightarrow> bool" (infixr "===>\<^sub>T" 55) where
  "rel_fun_lifted R R' \<equiv> R ===> crel_vs R'"
term 0 (**)

lemma "crel_vs = crel_vs_alt"
  unfolding crel_vs_def crel_vs_alt_def
  by (fastforce split: pred_prod_split)

definition consistentDP :: "('param =='mem\<Longrightarrow> 'result) \<Rightarrow> bool" where
  "consistentDP \<equiv> (op = ===> crel_vs op =) dp"
term 0 (**)
  
  (* cmem *)
lemma cmem_intro:
  assumes "\<And>param v. mem_map M param = Some v \<Longrightarrow> v = dp param"
  shows "cmem M"
  using assms unfolding cmem_def keys_dom_lookup by blast
term 0 (**)
  
lemma cmem_dest:
  assumes "cmem M" "mem_map M param = Some v"
  shows "v = dp param"
  using assms unfolding cmem_def dom_def keys_dom_lookup by auto
term 0 (**)
  
lemma cmem_empty:
  "cmem empty_mem"
  by (auto intro: cmem_intro simp: empty_correct)

  (* crel_vs *)
lemma crel_vs_intro:
  assumes "\<And>M v' M'. \<lbrakk>cmem M; runState v\<^sub>T M = (v', M')\<rbrakk> \<Longrightarrow> R v v' \<and> cmem M'"
  shows "crel_vs R v v\<^sub>T"
  using assms unfolding crel_vs_def by blast
term 0 (**)
  
lemma crel_vs_elim:
  assumes "crel_vs R v v\<^sub>T" "cmem M"
  obtains v' M' where "runState v\<^sub>T M = (v', M')" "R v v'" "cmem M'"
  using assms unfolding crel_vs_def by blast
term 0 (**)
  
  (* consistentDP *)
lemma consistentDP_intro:
  assumes "\<And>param. crel_vs (op =) (dp param) (dp\<^sub>T param)"
  shows "consistentDP dp\<^sub>T"
  using assms unfolding consistentDP_def by blast

lemma consistentDP_elim:
  assumes "consistentDP dp\<^sub>T" "cmem M"
  obtains v M' where "runState (dp\<^sub>T n) M = (v, M')" "v = dp n" "cmem M'"
  using assms unfolding consistentDP_def by (fastforce elim: crel_vs_elim dest: rel_funD)

corollary consistentDP_entry:
  assumes "consistentDP dp\<^sub>T"
  shows "fst (runState (dp\<^sub>T n) empty_mem) = dp n"
  by (rule consistentDP_elim[OF assms cmem_empty, of n]) simp
  
  
term 0 (**)
  
lemma crel_vs_return:
  "\<lbrakk>R x y\<rbrakk> \<Longrightarrow> crel_vs R x (return y)"
  unfolding return_def by (fastforce intro: crel_vs_intro)
term 0 (**)
  
lemma crel_vs_bind:
  assumes "crel_vs R0 v v'" "\<And>v v'. R0 v v' \<Longrightarrow> crel_vs R1 (f v) (f' v')"
  shows "crel_vs R1 (f v) (v' \<bind> f')"
  using assms unfolding bind_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim)

  (* Low level operators *)
lemma cmem_update:
  assumes "cmem M" "v = dp param" "runState (update param v) M = (u, M')"
  shows "cmem M'"
  using update_correct assms by (fastforce intro!: cmem_intro dest: cmem_dest split: if_splits)
term 0(**)

  
lemma crel_vs_get:
  "\<lbrakk>\<And>M. cmem M \<Longrightarrow> crel_vs R v (sf M)\<rbrakk> \<Longrightarrow> crel_vs R v (get \<bind> sf)"
  unfolding get_def bind_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim)
term 0 (**)
  
lemma crel_vs_put:
  "\<lbrakk>crel_vs R v sf; cmem M\<rbrakk> \<Longrightarrow> crel_vs R v (put M \<then> sf)"
  unfolding put_def bind_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim)
term 0 (**)

lemma crel_vs_checkmem:
  "\<lbrakk>crel_vs op = (dp param) s\<rbrakk> \<Longrightarrow> crel_vs op = (dp param) (checkmem param s)"
  unfolding checkmem_def
  oops

lemma cmem_lookup:
  "cmem M'" if "cmem M" "runState (lookup param) M = (v, M')"
  using lookup_correct[of param M] that unfolding cmem_def map_le_def by force


lemma crel_vs_lookup:
  "crel_vs (\<lambda> v v'. v = dp param \<and> (v'=Some v \<or> v'=None)) (dp param) (lookup param)"
  by (auto intro: crel_vs_intro dest: cmem_lookup cmem_dest lookup_correct)

lemma crel_vs_update:
  "crel_vs op = () (update param (dp param))"
  by (auto intro: cmem_update crel_vs_intro)

lemma crel_vs_bind_eq:
  "\<lbrakk>crel_vs op = v s; crel_vs R (f v) (sf v)\<rbrakk> \<Longrightarrow> crel_vs R (f v) (s \<bind> sf)"
  unfolding bind_def rel_fun_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim split: prod.split)
term 0 (**)

lemma crel_vs_checkmem:
  "\<lbrakk>crel_vs op = (dp param) s\<rbrakk> \<Longrightarrow> crel_vs op = (dp param) (checkmem param s)"
  unfolding checkmem_def
  by (rule crel_vs_bind[OF crel_vs_lookup]) (auto intro!: crel_vs_return crel_vs_update crel_vs_bind_eq crel_vs_lookup)
  
  (** Transfer rules **)
  (* Basics *)
lemma return_transfer[transfer_rule]:
  "(R ===>\<^sub>T R) (\<lambda>x. x) return"
  unfolding rel_fun_def by (metis crel_vs_return)
    
lemma bind_transfer[transfer_rule]:
  "(crel_vs R0 ===> (R0 ===>\<^sub>T R1) ===> crel_vs R1) (\<lambda>v f. f v) (op \<bind>)"
  unfolding rel_fun_def by (metis crel_vs_bind)

lemma fun_app_lifted_transfer[transfer_rule]:
  "(crel_vs (R0 ===>\<^sub>T R1) ===> crel_vs R0 ===> crel_vs R1) (\<lambda> f x. f x) (op .)"
  unfolding fun_app_lifted_def by transfer_prover
    
lemma crel_vs_fun_app:
  "\<lbrakk>crel_vs (R0 ===>\<^sub>T R1) f f\<^sub>T; crel_vs R0 x x\<^sub>T\<rbrakk> \<Longrightarrow> crel_vs R1 (f x) (f\<^sub>T . x\<^sub>T)"
  using fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD] .
    
term 0 (**)

lemma unlift_'_transfer[transfer_rule]:
  "(R ===> crel_vs R) (\<lambda> x. x) unlift_'"
  unfolding unlift_'_def by transfer_prover
term 0 (**)
  
lemma unlift_3_transfer[transfer_rule]:
  "((R0 ===>\<^sub>T R1) ===> (R0 ===> crel_vs R1)) (\<lambda> f x. f x) unlift_3"
  unfolding unlift_3_def by transfer_prover
term 0 (**)
  
lemma unlift_33_transfer[transfer_rule]:
  "((R0 ===>\<^sub>T R1 ===>\<^sub>T R2) ===> (R0 ===> R1 ===> crel_vs R2)) (\<lambda> f x0 x1. f x0 x1) unlift_33"
  unfolding unlift_33_def by transfer_prover

lemma lift_'_transfer[transfer_rule]:
  "(R ===> crel_vs R) (\<lambda> x. x) lift_'"
  unfolding lift_'_def by transfer_prover

lemma lift_3_transfer[transfer_rule]:
  "((R0 ===> R1) ===> crel_vs (R0 ===>\<^sub>T R1)) (\<lambda> f x. f x) lift_3"
  unfolding lift_3_def by transfer_prover
    
lemma lift_33_transfer[transfer_rule]:
  "((R0 ===> R1 ===> R2) ===> crel_vs (R0 ===>\<^sub>T R1 ===>\<^sub>T R2)) (\<lambda> f x0 x1. f x0 x1) lift_33"
  unfolding lift_33_def by transfer_prover

lemma lift_333_transfer[transfer_rule]:
  "((R0 ===> R1 ===> R2 ===> R3) ===> crel_vs (R0 ===>\<^sub>T R1 ===>\<^sub>T R2 ===>\<^sub>T R3)) (\<lambda> f x0 x1 x2. f x0 x1 x2) lift_333"
  unfolding lift_333_def by transfer_prover
term 0 (**)

  (* HOL *)
lemma If_transfer[transfer_rule]:
  "crel_vs (op = ===>\<^sub>T R ===>\<^sub>T R ===>\<^sub>T R) If If\<^sub>T"
  unfolding If\<^sub>T_def by transfer_prover
  
lemma id_transfer[transfer_rule]:
  "crel_vs (R ===>\<^sub>T R) id id\<^sub>T"
  unfolding id_def id\<^sub>T_def by transfer_prover
    
lemma comp_transfer[transfer_rule]:
  "crel_vs ((R1 ===>\<^sub>T R2) ===>\<^sub>T (R0 ===>\<^sub>T R1) ===>\<^sub>T (R0 ===>\<^sub>T R2)) comp comp\<^sub>T"
  unfolding comp_def comp\<^sub>T_def fun_app_lifted_def by transfer_prover
term 0 (**)

  (* Arithmetic *)

lemma plus_transfer[transfer_rule]:
  "crel_vs (op = ===>\<^sub>T op = ===>\<^sub>T op =) plus plus\<^sub>T"
  unfolding plus\<^sub>T_def by transfer_prover
  
lemma min_transfer[transfer_rule]:
  "crel_vs (op = ===>\<^sub>T op = ===>\<^sub>T op =) min min\<^sub>T"
  unfolding min\<^sub>T_def by transfer_prover
    
lemma max_transfer[transfer_rule]:
  "crel_vs (op = ===>\<^sub>T op = ===>\<^sub>T op =) max max\<^sub>T"
  unfolding max\<^sub>T_def by transfer_prover
term 0 (**)  

  (* Option *)
lemma case_option_transfer[transfer_rule]:
  "crel_vs (R1 ===>\<^sub>T (R0 ===>\<^sub>T R1) ===>\<^sub>T rel_option R0 ===>\<^sub>T R1) case_option case_option\<^sub>T"
  unfolding case_option\<^sub>T_def by transfer_prover

lemma None_transfer[transfer_rule]:
  "crel_vs (rel_option R) None None\<^sub>T"
  unfolding None\<^sub>T_def by transfer_prover

lemma Some_transfer[transfer_rule]:
  "crel_vs (R ===>\<^sub>T rel_option R) Some Some\<^sub>T"
  unfolding Some\<^sub>T_def by transfer_prover
term 0 (**)

  (* List *)  
lemma case_list_transfer[transfer_rule]:
  "crel_vs (R1 ===>\<^sub>T (R0 ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1) case_list case_list\<^sub>T"
  unfolding case_list\<^sub>T_def by transfer_prover
  
lemma Nil_transfer[transfer_rule]:
  "crel_vs (list_all2 R) Nil Nil\<^sub>T"
  unfolding Nil\<^sub>T_def by transfer_prover

lemma Cons_transfer[transfer_rule]:
  "crel_vs (R ===>\<^sub>T list_all2 R ===>\<^sub>T list_all2 R) Cons Cons\<^sub>T"
  unfolding Cons\<^sub>T_def by transfer_prover
    
lemma upt_transfer[transfer_rule]:
  "crel_vs (op = ===>\<^sub>T op = ===>\<^sub>T list_all2 op =) upt upt\<^sub>T"
  unfolding upt\<^sub>T_def by transfer_prover
term 0 (**)
  
  (* Prod *)
lemma case_prod_transfer[transfer_rule]:
  "crel_vs ((R0 ===>\<^sub>T R1 ===>\<^sub>T R2) ===>\<^sub>T rel_prod R0 R1 ===>\<^sub>T R2) case_prod case_prod\<^sub>T"
  unfolding case_prod\<^sub>T_def by transfer_prover
term 0 (**)
  
lemma Pair_transfer[transfer_rule]:
  "crel_vs (R0 ===>\<^sub>T R1 ===>\<^sub>T rel_prod R0 R1) Pair Pair\<^sub>T"
  unfolding Pair\<^sub>T_def by transfer_prover
term 0 (**)

  (* Combinator *)
lemma map_transfer[transfer_rule]:
  "crel_vs ((R0 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T list_all2 R1) map map\<^sub>T"
proof -
  have [transfer_rule]: "((R0 ===>\<^sub>T R1) ===> (list_all2 R0 ===>\<^sub>T list_all2 R1)) map map\<^sub>T'"
    apply ((rule rel_funI)+, induct_tac rule: list_all2_induct, assumption; unfold list.map map\<^sub>T'.simps)
    subgoal premises [transfer_rule] by transfer_prover
    subgoal premises [transfer_rule] by transfer_prover
    done
  show ?thesis
    unfolding map\<^sub>T_def by transfer_prover
qed
  
lemma fold_transfer[transfer_rule]:
  "crel_vs ((R0 ===>\<^sub>T R1 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1 ===>\<^sub>T R1) fold fold\<^sub>T"
proof -
  have [transfer_rule]: "((R0 ===>\<^sub>T R1 ===>\<^sub>T R1) ===> list_all2 R0 ===>\<^sub>T R1 ===>\<^sub>T R1) fold fold\<^sub>T'"
    apply ((rule rel_funI)+, induct_tac rule: list_all2_induct, assumption; unfold fold.simps fold\<^sub>T'.simps)
    subgoal premises [transfer_rule] by transfer_prover
    subgoal premises [transfer_rule] by transfer_prover
    done
  show ?thesis
    unfolding fold\<^sub>T_def by transfer_prover
qed
  
definition "and_leftp R P x y \<equiv> R x y \<and> P x"

lemma eq_onp_and_leftp_eq: "and_leftp (op =) P x y \<longleftrightarrow> eq_onp P x y"
  unfolding and_leftp_def eq_onp_def by auto

lemma and_leftp_elim: "and_leftp R P x y \<Longrightarrow> (R x y \<Longrightarrow> P x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding and_leftp_def by auto
term 0 (**)

lemma and_leftp_leftset_intro:
  "list_all2 R xs xs\<^sub>T' \<Longrightarrow> list_all2 (and_leftp R (\<lambda>x. x\<in>set xs)) xs xs\<^sub>T'"
  unfolding list_all2_iff and_leftp_def set_zip by auto
term 0 (**)
  
lemma and_leftp_lefteq_elim:
  assumes "and_leftp R (op = y) x x\<^sub>T'"
  obtains "x = y" "R y x\<^sub>T'"
  using assms unfolding and_leftp_def by auto

lemma and_leftp_lefteq_same:
  "R x x\<^sub>T' \<Longrightarrow> and_leftp R (op = x) x x\<^sub>T'"
  unfolding and_leftp_def by auto

lemma and_leftp_crel_vs:
  "and_leftp (crel_vs R) P x x\<^sub>T \<Longrightarrow> crel_vs (and_leftp R P) x x\<^sub>T"
  unfolding and_leftp_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim)
term 0 (**)

lemma map_transfer_inset:
   "crel_vs ((and_leftp R0 (\<lambda>x. x\<in>set xs) ===>\<^sub>T R1) ===>\<^sub>T and_leftp (list_all2 R0) (op = xs) ===>\<^sub>T (list_all2 R1)) map map\<^sub>T"
proof -
  { fix f f\<^sub>T' xs\<^sub>T'
    assume [transfer_rule]: "(and_leftp R0 (\<lambda>x. x\<in>set xs) ===>\<^sub>T R1) f f\<^sub>T'" and rx: "list_all2 R0 xs xs\<^sub>T'"
    from rx[THEN and_leftp_leftset_intro] have "crel_vs (list_all2 R1) (map f xs) (map\<^sub>T' f\<^sub>T' xs\<^sub>T')"
      apply (induction rule: list_all2_induct; unfold list.map map\<^sub>T'.simps)
      subgoal premises [transfer_rule] by transfer_prover
      subgoal premises [transfer_rule] by transfer_prover
      done
  }
  hence [transfer_rule]: "((and_leftp R0 (\<lambda>x. x\<in>set xs) ===>\<^sub>T R1) ===> and_leftp (list_all2 R0) (op = xs) ===>\<^sub>T (list_all2 R1)) map map\<^sub>T'" 
    by (fastforce elim: and_leftp_lefteq_elim)
  show ?thesis
    unfolding map\<^sub>T_def by transfer_prover
qed

lemma map_transfer_inset_unfolded:
  fixes R0 R1 f f\<^sub>T' xs xs\<^sub>T
  assumes "(and_leftp R0 (\<lambda>x. x\<in>set xs) ===>\<^sub>T R1) f f\<^sub>T'" "crel_vs (list_all2 R0) xs xs\<^sub>T"
  shows "crel_vs (list_all2 R1) (map f xs) (map\<^sub>T . \<langle>f\<^sub>T'\<rangle> . xs\<^sub>T)"
  apply (rule fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD, where x=xs])
   apply (rule fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD, where x=f])
    apply (fact map_transfer_inset)
   apply (rule crel_vs_return)
   apply (fact assms(1))
  apply (rule and_leftp_crel_vs)
  apply (rule and_leftp_lefteq_same)
  apply (fact assms(2))
  done

lemma map_transfer_inset_unfolded':
  fixes R0 R1 f f\<^sub>T' xs xs\<^sub>T
  assumes "\<And>x x\<^sub>T'. R0 x x\<^sub>T' \<Longrightarrow> x\<in>set xs \<Longrightarrow> crel_vs R1 (f x) (f\<^sub>T' x\<^sub>T')" "crel_vs (list_all2 R0) xs xs\<^sub>T"
  shows "crel_vs (list_all2 R1) (map f xs) (map\<^sub>T . \<langle>f\<^sub>T'\<rangle> . xs\<^sub>T)"
  apply (rule map_transfer_inset_unfolded)
   apply (rule rel_funI)
   apply (rule assms(1))
    apply (erule and_leftp_elim[where R=R0])
    apply (assumption)
   apply (erule and_leftp_elim[where R=R0])
   apply (assumption)
  apply (fact assms(2))
  done

lemma crel_vs_map_simple:
  fixes R f f\<^sub>T' xs xs\<^sub>T
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> crel_vs op = (f x) (f\<^sub>T' x)" "crel_vs op = xs xs\<^sub>T"
  shows "crel_vs op = (map f xs) (map\<^sub>T . \<langle>f\<^sub>T'\<rangle> . xs\<^sub>T)"
  apply (rule map_transfer_inset_unfolded'[where ?R0.0="op =" and ?R1.0="op =", unfolded list.rel_eq])
   apply clarify
   apply (fact assms(1))
  apply (fact assms(2))
  done

lemma map_transfer_inset0:
  "crel_vs ((eq_onp (\<lambda>x. x\<in>set xs) ===>\<^sub>T R) ===>\<^sub>T eq_onp (op = xs) ===>\<^sub>T (list_all2 R)) map map\<^sub>T"
  using map_transfer_inset[of "op =", unfolded list.rel_eq eq_onp_and_leftp_eq] .
term 0 (**)

lemma fold_transfer_inset:
  fixes R0 R1 f f\<^sub>T' xs xs\<^sub>T
  assumes "(and_leftp R0 (\<lambda>x. x\<in>set xs) ===>\<^sub>T R1 ===>\<^sub>T R1) f f\<^sub>T'" "crel_vs (list_all2 R0) xs xs\<^sub>T"
  shows  "crel_vs (R1 ===>\<^sub>T R1) (fold f xs) (fold\<^sub>T . \<langle>f\<^sub>T'\<rangle> . xs\<^sub>T)"
proof -
  { fix f f\<^sub>T' xs\<^sub>T' a b
    assume [transfer_rule]: "(and_leftp R0 (\<lambda>x. x\<in>set xs) ===>\<^sub>T R1 ===>\<^sub>T R1) f f\<^sub>T'" and rx: "list_all2 R0 xs xs\<^sub>T'"
    from rx[THEN and_leftp_leftset_intro] have "crel_vs (R1 ===>\<^sub>T R1) (fold f xs) (fold\<^sub>T' f\<^sub>T' xs\<^sub>T')"
      apply (induction rule: list_all2_induct; unfold fold.simps fold\<^sub>T'.simps)
      subgoal premises [transfer_rule] by transfer_prover
      subgoal premises [transfer_rule] by transfer_prover
      done
  }
  hence [transfer_rule]: "((and_leftp R0 (\<lambda>x. x\<in>set xs) ===>\<^sub>T R1 ===>\<^sub>T R1) ===> and_leftp (list_all2 R0) (op = xs) ===>\<^sub>T R1 ===>\<^sub>T R1) fold fold\<^sub>T'" 
    by (fastforce elim: and_leftp_lefteq_elim)
  show ?thesis
    unfolding fold\<^sub>T_def supply [transfer_rule] = assms(1) and_leftp_lefteq_same[THEN and_leftp_crel_vs, OF assms(2)] by transfer_prover    
qed
  
end
end

definition K :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "K x \<equiv> eq_onp (op = x)"

lemma K_self: "K x x x"
  unfolding K_def eq_onp_def by auto

definition map_lookup where
  "map_lookup k \<equiv> do {
    m \<leftarrow> get;
    return (m k)
  }"

definition map_update where
  "map_update k v \<equiv> do {
    m \<leftarrow> get;
    let m' = m(k\<mapsto>v);
    put m'
  }"

locale pure_mem_def =
  fixes pure_lookup :: "'mem \<Rightarrow> 'param \<Rightarrow> 'result option"
    and pure_update :: "'mem \<Rightarrow> 'param \<Rightarrow> 'result \<Rightarrow> 'mem"
begin

definition lookup :: "'param \<Rightarrow> ('mem, 'result option) state" where
  "lookup k \<equiv> do {
    m \<leftarrow> get;
    return (pure_lookup m k)
  }"

definition update :: "'param \<Rightarrow> 'result \<Rightarrow> ('mem, unit) state" where
  "update k v \<equiv> do {
    m \<leftarrow> get;
    let m' = pure_update m k v;
    put m'
  }"

definition "mem_map \<equiv> pure_lookup"

end

interpretation hol_map_def: pure_mem_def "\<lambda>m k. m k" "\<lambda>m k v. m(k\<mapsto>v)" .


interpretation hol_map: mem_correct hol_map_def.lookup hol_map_def.update Map.empty hol_map_def.mem_map
  unfolding pure_mem_def.lookup_def pure_mem_def.update_def pure_mem_def.mem_map_def bind_def return_def get_def put_def
  by standard auto

interpretation rbt_map_def: pure_mem_def RBT.lookup "\<lambda>m k v. RBT.insert k v m" .

interpretation rbt_map: mem_correct rbt_map_def.lookup rbt_map_def.update RBT.empty rbt_map_def.mem_map
  unfolding pure_mem_def.lookup_def pure_mem_def.update_def pure_mem_def.mem_map_def bind_def return_def get_def put_def
  by standard (auto simp: lookup_update' lookup_empty)

locale dp_consistency_default =
  fixes dp :: "'param :: linorder \<Rightarrow> 'result"
begin

sublocale dp_consistency hol_map_def.update Map.empty hol_map_def.mem_map hol_map_def.lookup dp ..
sublocale rbt: dp_consistency rbt_map_def.update RBT.empty rbt_map_def.mem_map rbt_map_def.lookup dp ..

end

notepad begin
  interpret x: dp_consistency_default id .
  term x.rbt.consistentDP
end
