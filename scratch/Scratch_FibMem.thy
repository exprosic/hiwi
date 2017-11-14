theory Scratch_FibMem
  imports Refine_Imperative_HOL.IICF "dp/Monad"
begin

fun fib :: "nat \<Rightarrow> int" where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib (Suc n) + fib n"

lemma [simp]:
  "n < 2 \<Longrightarrow> fib n = 1"
  "\<not>(n < 2) \<Longrightarrow> fib n = fib (n-2) + fib (n-1)"
  by (cases n rule: fib.cases; simp)+

definition fib_spec :: "nat \<Rightarrow> int nres" where
  "fib_spec n \<equiv> RETURN (fib n)"

type_synonym tab = "int list"

(*Since fib n \<ge> 0, negative value is used here to represent None*)
definition is_some :: "int \<Rightarrow> bool" where
  "is_some v \<equiv> v \<ge> 0"

definition checkmem :: "tab \<Rightarrow> nat \<Rightarrow> (int \<times> tab) nres \<Rightarrow> (int \<times> tab) nres" where
  "checkmem M n v \<equiv> do {
    fn \<leftarrow> mop_list_get M n;
    if is_some fn
      then RETURN (fn, M)
      else do {
        (fn, M) \<leftarrow> v;
        M \<leftarrow> mop_list_set M n fn;
        RETURN (fn, M)
      }
    }"

definition fib_rec_mem_body :: "((nat \<times> tab) \<Rightarrow> (int \<times> tab) nres) \<Rightarrow> ((nat \<times> tab) \<Rightarrow> (int \<times> tab) nres)" where
  "fib_rec_mem_body \<equiv> \<lambda>f (n, M). checkmem M n (do {
    if n < 2
      then RETURN (1, M)
      else do {
        (f0, M) \<leftarrow> f (n-2, M);
        (f1, M) \<leftarrow> f (n-1, M);
        RETURN (f0 + f1, M)
      }
  })"

definition fib_rec_mem :: "nat \<Rightarrow> int nres" where
  "fib_rec_mem n \<equiv> do {
    (v, _) \<leftarrow> RECT fib_rec_mem_body (n, replicate (n+1) (-1));
    RETURN v
  }"

sepref_definition fib_rec_mem1 is fib_rec_mem :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a int_assn"
  unfolding fib_rec_mem_def fib_rec_mem_body_def checkmem_def is_some_def
  apply (rewrite in "RECT _ (_, \<hole>_)" array_fold_custom_of_list)
  by sepref

export_code fib_rec_mem1 checking SML_imp
export_code fib_rec_mem1 in SML_imp module_name FibMem
(*
abbreviation "nres_bind \<equiv> Refine_Basic.bind"
abbreviation "state_bind \<equiv> Monad.bind"
*)

datatype ('M, 'a) stateT = StateT (runStateT: "'M \<Rightarrow> ('a \<times> 'M) nres")
term 0 (**)

definition returnT :: "'a \<Rightarrow> ('M, 'a) stateT" where
  "returnT a \<equiv> StateT (\<lambda>M. RETURN (a, M))"

definition bindT :: "('M, 'a) stateT \<Rightarrow> ('a \<Rightarrow> ('M, 'b) stateT) \<Rightarrow> ('M, 'b) stateT" where
  "bindT s f \<equiv> StateT (\<lambda>M. do {
    (v, M') \<leftarrow> runStateT s M;
    runStateT (f v) M'
  })"

adhoc_overloading
  Monad_Syntax.bind bindT

definition getT :: "('M, 'M) stateT" where
  "getT \<equiv> StateT (\<lambda>M. RETURN (M, M))"

definition putT :: "'M \<Rightarrow> ('M, unit) stateT" where
  "putT M \<equiv> StateT (\<lambda>M. RETURN ((), M))"

definition liftT :: "'a nres \<Rightarrow> ('M, 'a) stateT" where
  "liftT nr = StateT (\<lambda>M. do {v \<leftarrow> nr; RETURN (v, M)})"

definition checkmemT :: "nat \<Rightarrow> (tab, int) stateT \<Rightarrow> (tab, int) stateT" where
  "checkmemT n s \<equiv> do {
    M \<leftarrow> getT;
    Mn \<leftarrow> liftT (mop_list_get M n);
    if is_some Mn
      then returnT Mn
      else do {
        v \<leftarrow> s;
        M' \<leftarrow> liftT (mop_list_set M n v);
        putT M';
        returnT v
      }
  }"

definition fib_rec_mem_body' :: "((nat \<times> tab) \<Rightarrow> (int \<times> tab) nres) \<Rightarrow> ((nat \<times> tab) \<Rightarrow> (int \<times> tab) nres)" where
  "fib_rec_mem_body' \<equiv> \<lambda>f (n, M). runStateT (checkmemT n (do {
    if n<2
      then returnT 1
      else do {
        f0 \<leftarrow> StateT (curry f (n-2));
        f1 \<leftarrow> StateT (curry f (n-1));
        returnT (f0 + f1)
      }
    })) M"

definition cmem :: "tab \<Rightarrow> bool" where
  "cmem M \<equiv> \<forall>i. i<length M \<longrightarrow> is_some (M!i) \<longrightarrow> M!i=fib i"

lemma cmem_intro:
  assumes "\<And>i. i<length M \<Longrightarrow> is_some (M!i) \<Longrightarrow> M!i=fib i"
  shows "cmem M"
  using assms unfolding cmem_def is_some_def by fastforce

lemma cmem_elim:
  assumes "cmem M" "i < length M" "is_some (M!i)"
  obtains "fib i = M!i "
  using assms unfolding cmem_def by fastforce

lemma cmem_update:
  "\<lbrakk>cmem M; v = fib i\<rbrakk> \<Longrightarrow> cmem (list_update M i v)"
  by (fastforce intro!: cmem_intro elim: cmem_elim simp: nth_list_update')

definition crel_vs :: "'a nres \<Rightarrow> (tab, 'a) stateT \<Rightarrow> bool" where
  "crel_vs nr s \<equiv> \<forall>M. cmem M \<longrightarrow> (case runStateT s M of
    FAILi \<Rightarrow> nr=FAIL
  | RES vM \<Rightarrow> RES (fst`vM) \<le> nr \<and> Ball (snd`vM) cmem)"

context
  fixes N :: nat
begin

definition fib_rec_mem' :: "int nres" where
  "fib_rec_mem' \<equiv> do {
    (v, _) \<leftarrow> RECT fib_rec_mem_body' (N, replicate (N+1) (-1));
    RETURN v
  }"

definition param_isvalid :: "nat \<Rightarrow> tab \<Rightarrow> bool" where
  "param_isvalid n M \<equiv> n < length M \<and> length M = N+1 \<and> cmem M"

definition fib_mem_spec :: "(nat \<times> tab) \<Rightarrow> (int \<times> tab) nres" where
  "fib_mem_spec \<equiv> \<lambda>(n, M). SPEC (\<lambda>(v, M'). fib n = v \<and> param_isvalid n M')"

lemma checkmemT_vcg_rule:
  fixes n s M spec
  assumes "param_isvalid n M \<Longrightarrow> runStateT s M \<le> fib_mem_spec (n, M)" "param_isvalid n M"
  shows "runStateT (checkmemT n s) M \<le> fib_mem_spec (n, M)"
  unfolding checkmemT_def bindT_def getT_def putT_def liftT_def
  apply auto
  subgoal
    apply (refine_vcg)
    apply (unfold returnT_def RETURN_def fib_mem_spec_def)
    using assms(2) apply (auto simp: param_isvalid_def elim: cmem_elim)
    done
  subgoal
    apply (refine_vcg)
    subgoal using assms(2) by (auto simp: param_isvalid_def)
    apply (unfold returnT_def RETURN_def fib_mem_spec_def)
    apply refine_vcg
    apply clarsimp
    apply (intro assms(1)[unfolded fib_mem_spec_def, simplified] assms(2))
    done
  done

lemma blah:
  "runStateT (if b then StateT sx else StateT sy) = (if b then sx else sy)"
  "(if b then fx else fy) x = (if b then fx x else fy x)"
  by auto

lemma fib_rec_mem_refine_aux:
  "(RECT fib_rec_mem_body', fib_mem_spec) \<in> (br id (uncurry param_isvalid)) \<rightarrow> \<langle>Id\<times>\<^sub>rId\<rangle>nres_rel"
  apply (clarsimp simp: uncurry_def in_br_conv intro!: nres_relI)
  apply (rule RECT_rule[where V="fst <*mlex*> {}" and pre="uncurry param_isvalid"])
  defer
  subgoal by (simp add: wf_mlex)
  subgoal by (simp add: param_isvalid_def)
  subgoal premises prems for n M f nM
    thm prems
    apply (unfold fib_rec_mem_body'_def)
    apply (auto split: prod.split)
    subgoal for x' M'
      apply (rule checkmemT_vcg_rule)
      defer
      subgoal using prems(3) unfolding param_isvalid_def by simp
      subgoal unfolding fib_mem_spec_def returnT_def
        apply refine_vcg
        apply auto
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
          subgoal unfolding fib_mem_spec_def param_isvalid_def apply auto done
          done
        done
      done
    done
  subgoal
    unfolding fib_rec_mem_body'_def checkmemT_def getT_def putT_def bindT_def liftT_def curry_def returnT_def
    is_some_def
    unfolding blah
    unfolding stateT.sel
    apply auto
    apply refine_mono
    done
  done

corollary fib_rec_mem_refine:
  "(fib_rec_mem', fib_spec N) \<in> \<langle>Id\<rangle>nres_rel"
proof (clarsimp intro!: nres_relI)
  have *:"local.param_isvalid n M \<Longrightarrow>
       REC\<^sub>T fib_rec_mem_body' (n, M) \<le> local.fib_mem_spec (n, M)" for n M
    using fib_rec_mem_refine_aux by (auto simp: uncurry_def in_br_conv dest!: fun_relD nres_relD)
  show "fib_rec_mem' \<le> fib_spec N"
    apply (unfold fib_rec_mem'_def fib_spec_def)
    apply (refine_vcg order_trans[OF *])
      subgoal
        unfolding param_isvalid_def
        apply (auto simp add: is_some_def simp del: replicate_Suc intro!: cmem_intro)
        done
      subgoal
        unfolding fib_mem_spec_def
        apply auto
        done
      done
  qed

  
end
end