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
  assumes "cmem M" "i < length M"
  obtains "M!i = Some (fib i)" | "M!i = None"
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

definition param_isvalid :: "nat \<Rightarrow> bool" where
  "param_isvalid n \<equiv> n < N+1"

definition mem_isvalid :: "tab \<Rightarrow> bool" where
  "mem_isvalid M \<equiv> cmem M \<and> length M = N+1"

lemma mem_param_isvalid_elim:
  assumes "mem_isvalid M" "param_isvalid n"
  obtains "n < length M \<and> M!n = Some (fib n)" | "n < length M \<and> M!n = None"
  using assms unfolding mem_isvalid_def param_isvalid_def by (fastforce elim: cmem_elim)

definition fib_mem_spec :: "(nat \<times> tab) \<Rightarrow> (int \<times> tab) nres" where
  "fib_mem_spec \<equiv> \<lambda>(n, M). SPEC (\<lambda>(v, M'). fib n = v \<and> length M' = N+1 \<and> cmem M')"

definition crel_nt :: "'a nres \<Rightarrow> (tab, 'a) stateT \<Rightarrow> bool" where
  "crel_nt nv t \<equiv>
    \<forall>M. mem_isvalid M \<longrightarrow>
      (let np = runStateT t M in
        do {(v, M') \<leftarrow> np; ASSERT (mem_isvalid M'); RETURN v} \<le> nv)"

lemma crel_nt_intro:
  fixes nv t
  assumes "\<And>M. mem_isvalid M \<Longrightarrow> do {(v, M') \<leftarrow> runStateT t M; ASSERT (mem_isvalid M'); RETURN v} \<le> nv"
  shows "crel_nt nv t"
  unfolding crel_nt_def using assms by auto

lemma crel_nt_dest:
  assumes "crel_nt nv t" "mem_isvalid M"
  shows "do {(v, M') \<leftarrow> runStateT t M; ASSERT (mem_isvalid M'); RETURN v} \<le> nv"
  using assms(1)[unfolded crel_nt_def, rule_format, OF assms(2)] by auto

definition fib_spec_at :: "nat \<Rightarrow> int nres" where
  "fib_spec_at n \<equiv> do {
    ASSERT (param_isvalid n);
    RETURN (fib n)
  }"

definition fib_spec :: "int nres" where
  "fib_spec \<equiv> RETURN (fib N)"

lemma "fib_spec = fib_spec_at N"
  unfolding fib_spec_def fib_spec_at_def param_isvalid_def by auto

lemma crel_nt_getT:
  assumes "\<And>M. mem_isvalid M \<Longrightarrow> crel_nt nr (tf M)"
  shows "crel_nt nr (getT \<bind> tf)"
  using assms by (fastforce simp: getT_def bindT_def intro: crel_nt_intro dest: crel_nt_dest)

lemma crel_nt_putT:
  assumes "crel_nt nr t" "mem_isvalid M"
  shows "crel_nt nr (putT M \<then> t)"
  using assms by (fastforce simp: putT_def bindT_def intro: crel_nt_intro dest: crel_nt_dest)

lemma crel_nt_liftT:
  assumes "nr1 \<le> nr0"
  shows "crel_nt nr0 (liftT nr1)"
  using assms by (fastforce simp: liftT_def intro: crel_nt_intro)

lemma mem_isvalid_nres:
  assumes "mem_isvalid M" "param_isvalid n"
  shows "mop_list_get M n \<le> SPEC (\<lambda>v. v=None \<or> v=Some (fib n))"
  using assms by (refine_vcg) (auto elim: mem_param_isvalid_elim)

lemma crel_nt_bind_pure:
  assumes "crel_nt (SPEC \<Phi>) t" "\<And>v. \<Phi> v \<Longrightarrow> crel_nt nr (tf v)"
  shows "crel_nt nr (t \<bind> tf)"
  unfolding bindT_def
  apply (rule crel_nt_intro)
  apply (unfold stateT.sel)
  subgoal premises prems
    thm crel_nt_dest[OF assms(1) prems]
    thm crel_nt_dest[OF assms(2) prems]
    thm bind_le_shift bind_rule_complete
    apply (unfold bind_le_shift)
    apply (rule crel_nt_dest[OF assms(1) prems, unfolded bind_le_shift, THEN order_trans])
    apply auto
    unfolding ASSERT_le_iff
    apply auto
    subgoal premises prems'
      thm prems'
      apply (rule crel_nt_dest[OF assms(2) prems'(2), OF prems'(3), unfolded bind_le_shift, THEN order_trans])
      apply auto
      apply (fact prems'(1))
      done
    done
  done

lemma crel_nt_spec_at_intro:
  assumes "param_isvalid n \<Longrightarrow> crel_nt (RETURN (fib n)) t"
  shows "crel_nt (fib_spec_at n) t"
  unfolding fib_spec_at_def
  apply (rule crel_nt_intro)
  apply (auto simp: bind_le_shift)
  apply (unfold pw_bind_nofail)
  apply auto
  apply (unfold pw_ASSERT)
  apply (frule assms)
  subgoal premises prems
    apply (rule crel_nt_dest[OF prems(3) prems(1), unfolded bind_le_shift, THEN order_trans])
    apply auto
    apply (refine_vcg)
     apply auto
    unfolding ireturn_eq
    unfolding assert_bind_spec_conv
    apply auto
    done
  done

lemma crel_nt_spec_at_dest:
  assumes "crel_nt (fib_spec_at n) t" "param_isvalid n"
  shows "crel_nt (RETURN (fib n)) t"
  apply (rule crel_nt_intro)
  apply (frule crel_nt_dest[OF assms(1)])
  unfolding fib_spec_at_def
  unfolding le_ASSERT_iff
  using assms(2) apply auto
  done

lemma crel_nt_returnT:
  "crel_nt (RETURN v) (returnT v)"
  unfolding returnT_def by (fastforce intro: crel_nt_intro)

lemma crel_nt_checkmemT:
  assumes "crel_nt (fib_spec_at n) t"
  shows "crel_nt (fib_spec_at n) (checkmemT n t)"
  apply (rule crel_nt_spec_at_intro)
  apply (unfold checkmemT_def)
  apply (rule crel_nt_getT)
  apply (rule crel_nt_bind_pure)
   apply (rule crel_nt_liftT)
   apply (rule mem_isvalid_nres)
    apply (assumption)
   apply (assumption)
  apply auto
  defer
   apply (rule crel_nt_returnT)
  apply (rule crel_nt_bind_pure)
  apply (rule assms[THEN crel_nt_spec_at_dest, unfolded ireturn_eq])
   apply assumption
  apply clarify
  apply (rule crel_nt_bind_pure)
   apply (rule crel_nt_liftT)
   apply (unfold assert_bind_spec_conv)
   apply (unfold mem_isvalid_def param_isvalid_def)[1]
  defer
   apply (rule crel_nt_putT)
    apply (rule crel_nt_returnT)
   apply assumption
  apply (unfold mem_isvalid_def)
  apply auto
  apply (rule cmem_update)
   apply auto
  done

  
  thm assert_bind_spec_conv
  oops
  thm Collect_mem_eq


  term 0 (*
lemma
  assumes "crel_nt nr0 nr"
  shows "crel_nt nr (liftT nr0 \<bind> tf)"
term 0 (*
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
        apply (auto simp: fib.simps param_isvalid_def)
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
