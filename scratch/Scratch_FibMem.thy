theory Scratch_FibMem
  imports Refine_Imperative_HOL.IICF
begin

fun fib :: "nat \<Rightarrow> int" where
  "fib n =
    (if n=0 then 1 else
     if n=1 then 1 else
     fib (n-2) + fib (n-1))"

declare fib.simps[simp del]

type_synonym tab = "int option list"

datatype ('M, 'a) stateT = StateT (runStateT: "'M \<Rightarrow> ('a \<times> 'M) nres")
term 0 (**)

definition returnT :: "'a \<Rightarrow> ('M, 'a) stateT" where
  "returnT a \<equiv> StateT (\<lambda>M. RETURN (a, M))"

definition bindT :: "('M, 'a) stateT \<Rightarrow> ('a \<Rightarrow> ('M, 'b) stateT) \<Rightarrow> ('M, 'b) stateT" where
  "bindT s f \<equiv> StateT (\<lambda>M. do {
    (*nres monad*)
    (v, M') \<leftarrow> runStateT s M;
    runStateT (f v) M'
  })"

adhoc_overloading
  Monad_Syntax.bind bindT

definition getT :: "('M, 'M) stateT" where
  "getT \<equiv> StateT (\<lambda>M. RETURN (M, M))"

definition putT :: "'M \<Rightarrow> ('M, unit) stateT" where
  "putT M \<equiv> StateT (\<lambda>_. RETURN ((), M))"

definition liftT :: "'a nres \<Rightarrow> ('M, 'a) stateT" where
  "liftT nr = StateT (\<lambda>M. do {
    (*nres monad*)
    v \<leftarrow> nr;
    RETURN (v, M)
  })"

definition checkmemT :: "nat \<Rightarrow> (tab, int) stateT \<Rightarrow> (tab, int) stateT" where
  "checkmemT n s \<equiv> do {
    (*stateT monad*)
    M \<leftarrow> getT;
    Mno \<leftarrow> liftT (mop_list_get M n);
    case Mno of
      Some Mn \<Rightarrow> returnT Mn
    | None \<Rightarrow> do {
        v \<leftarrow> s;
        M' \<leftarrow> liftT (mop_list_set M n (Some v));
        putT M';
        returnT v
      }
  }"

type_synonym ('a, 'b) recursor = "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"

definition unpack_body :: "('a, ('M, 'b) stateT) recursor \<Rightarrow> ('a \<times> 'M, ('b \<times> 'M) nres) recursor" where
  "unpack_body body \<equiv> \<lambda>f (n, M). runStateT (body ((StateT oo curry) f) n) M"

definition cmem :: "tab \<Rightarrow> bool" where
  "cmem M \<equiv> \<forall>i v. i<length M \<longrightarrow> M!i = Some v \<longrightarrow> v=fib i"

lemma cmem_intro:
  assumes "\<And>i v. i<length M \<Longrightarrow> M!i = Some v \<Longrightarrow> v=fib i"
  shows "cmem M"
  using assms unfolding cmem_def by fastforce

lemma cmem_elim:
  assumes "cmem M" "i < length M" "M!i = Some v"
  obtains "v = fib i"
  using assms unfolding cmem_def by fastforce

lemma cmem_update:
  "\<lbrakk>cmem M; v = fib i\<rbrakk> \<Longrightarrow> cmem (list_update M i (Some v))"
  by (fastforce intro!: cmem_intro elim: cmem_elim simp: nth_list_update' split: if_splits)

(*
definition crel_vs :: "'a nres \<Rightarrow> (tab, 'a) stateT \<Rightarrow> bool" where
  "crel_vs nr s \<equiv> \<forall>M. cmem M \<longrightarrow> (case runStateT s M of
    FAILi \<Rightarrow> nr=FAIL
  | RES vM \<Rightarrow> RES (fst`vM) \<le> nr \<and> Ball (snd`vM) cmem)"
*)

context
  fixes N :: nat
begin

definition fib_spec :: "int nres" where
  "fib_spec \<equiv> RETURN (fib N)"

definition fib_rec_mem_body' :: "(nat, (tab, int) stateT) recursor" where
  "fib_rec_mem_body' \<equiv> \<lambda>f n. checkmemT n (do {
    (*stateT monad*)
    if n<2
      then returnT 1
      else do {
        f0 \<leftarrow> f (n-2);
        f1 \<leftarrow> f (n-1);
        returnT (f0 + f1)
      }
    })"

definition fib_rec_mem' :: "int nres" where
  "fib_rec_mem' \<equiv> do {
    (*nres monad*)
    (v, _) \<leftarrow> RECT (unpack_body fib_rec_mem_body') (N, replicate (N+1) None);
    RETURN v
  }"

definition param_isvalid :: "nat \<Rightarrow> tab \<Rightarrow> bool" where
  "param_isvalid n M \<equiv> n < length M \<and> length M = N+1 \<and> cmem M"

definition fib_mem_spec :: "(nat \<times> tab) \<Rightarrow> (int \<times> tab) nres" where
  "fib_mem_spec \<equiv> \<lambda>(n, M). SPEC (\<lambda>(v, M'). fib n = v \<and> param_isvalid n M')"

lemma checkmemT_vcg_rule:
  fixes n s M spec
  assumes "param_isvalid n M \<Longrightarrow> runStateT s M \<le> fib_mem_spec (n, M)"
  shows "param_isvalid n M \<Longrightarrow> runStateT (checkmemT n s) M \<le> fib_mem_spec (n, M)"
  unfolding checkmemT_def bindT_def getT_def putT_def liftT_def
  unfolding stateT.sel
  apply (auto split: option.splits)
  subgoal
    apply (unfold returnT_def RETURN_def fib_mem_spec_def param_isvalid_def)
    apply (refine_vcg order_trans[OF assms])
      apply (auto simp: fib_mem_spec_def param_isvalid_def intro!: cmem_update)
    done
  subgoal
    apply (refine_vcg)
    subgoal by (auto simp: param_isvalid_def)
    apply (unfold returnT_def RETURN_def fib_mem_spec_def)
    apply (refine_vcg order_trans[OF assms])
    apply (auto simp add: fib_mem_spec_def param_isvalid_def elim!: cmem_elim)
    done
  done

lemma if_distrib2:
  "(if b then fx else fy) x = (if b then fx x else fy x)"
  by simp

lemma fib_rec_mem_refine_aux:
  "(RECT (unpack_body fib_rec_mem_body'), fib_mem_spec) \<in> (br id (uncurry param_isvalid)) \<rightarrow> \<langle>Id\<times>\<^sub>rId\<rangle>nres_rel"
  apply (clarsimp simp: uncurry_def in_br_conv intro!: nres_relI)
  apply (rule RECT_rule[where V="fst <*mlex*> {}" and pre="uncurry param_isvalid"])
  subgoal premises
    unfolding fib_rec_mem_body'_def unpack_body_def
    unfolding checkmemT_def getT_def putT_def bindT_def liftT_def curry_def returnT_def
    unfolding option.case_distrib if_distrib stateT.sel if_distrib2
    unfolding stateT.sel comp_def
    apply refine_mono
    done
  subgoal by (simp add: wf_mlex)
  subgoal by (simp add: param_isvalid_def)
  subgoal premises prems for n M f nM
    thm prems
    apply (unfold fib_rec_mem_body'_def unpack_body_def)
    apply (auto split: prod.split)
    subgoal for x' M'
      apply (rule checkmemT_vcg_rule)
      defer
      subgoal using prems(3) unfolding param_isvalid_def by simp
      subgoal unfolding fib_mem_spec_def returnT_def
        apply refine_vcg
        apply (auto simp: fib.simps)
        done
      done
    subgoal for n' M'
      apply (rule checkmemT_vcg_rule)
      defer
      subgoal using prems(3) unfolding param_isvalid_def by auto
      subgoal unfolding fib_mem_spec_def returnT_def bindT_def
        apply (refine_vcg )
        apply (unfold stateT.sel)
        apply (unfold curry_def)
        apply (refine_vcg order_trans[OF prems(2)])
        subgoal using prems(3) unfolding param_isvalid_def by auto
        subgoal using prems(3) unfolding param_isvalid_def by (auto simp: mlex_eq)
        subgoal unfolding fib_mem_spec_def param_isvalid_def
          apply (refine_vcg order_trans[OF prems(2)])
          subgoal unfolding param_isvalid_def by auto
          subgoal by (auto simp: mlex_eq)
          subgoal
            unfolding fib_mem_spec_def param_isvalid_def apply auto
            apply (rewrite in "_ + _ = \<hole>" fib.simps)
            apply simp
            done
          done
        done
      done
    done
  done

corollary fib_rec_mem_refine:
  "(fib_rec_mem', fib_spec) \<in> \<langle>Id\<rangle>nres_rel"
proof (clarsimp intro!: nres_relI)
  have *:"local.param_isvalid n M \<Longrightarrow> REC\<^sub>T (unpack_body fib_rec_mem_body') (n, M) \<le> local.fib_mem_spec (n, M)" for n M
    using fib_rec_mem_refine_aux by (auto simp: uncurry_def in_br_conv dest!: fun_relD nres_relD)
  show "fib_rec_mem' \<le> fib_spec"
    apply (unfold fib_rec_mem'_def fib_spec_def)
    apply (refine_vcg order_trans[OF *])
    unfolding param_isvalid_def fib_mem_spec_def
     apply (auto simp del: replicate_Suc intro!: cmem_intro)
    done
  qed

end


end
