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

definition nres_fun_separated :: "('a \<Rightarrow> 'b nres) \<Rightarrow> bool" where
  "nres_fun_separated f \<equiv> FAIL \<in> range f \<longrightarrow> range f = {FAIL}"

lemma nres_fun_separated_intro:
  assumes "FAIL \<in> range f \<Longrightarrow> range f = {FAIL}"
  shows "nres_fun_separated f"
  using assms unfolding nres_fun_separated_def ..

lemma nres_fun_separated_dest:
  assumes "nres_fun_separated f" "FAIL \<in> range f"
  shows "range f = {FAIL}"
  using assms unfolding nres_fun_separated_def ..

typedef ('a, 'b) nres_fun = "Collect (nres_fun_separated :: ('a \<Rightarrow> 'b nres) \<Rightarrow> bool)"
  apply (rule exI[of _ top])
  unfolding nres_fun_separated_def
  apply auto
  done
lemma nres_fun_separated_iff
:
  "nres_fun_separated f \<longleftrightarrow> (\<forall>x y. f x = FAIL \<longrightarrow> f y = FAIL)"
  unfolding nres_fun_separated_def image_def by (auto; metis)

setup_lifting type_definition_nres_fun

instantiation nres_fun :: (type, type) complete_lattice
begin
(*
definition "f \<le> g \<equiv> Rep_nres_fun f \<le> Rep_nres_fun g"
definition "f < g \<equiv> Rep_nres_fun f < Rep_nres_fun g"
definition "inf f g \<equiv> Abs_nres_fun (inf (Rep_nres_fun f) (Rep_nres_fun g))"
*)
lift_definition less_eq_nres_fun :: "('a, 'b) nres_fun \<Rightarrow> ('a, 'b) nres_fun \<Rightarrow> bool" is "op \<le>" .
lift_definition less_nres_fun ::  "('a, 'b) nres_fun \<Rightarrow> ('a, 'b) nres_fun \<Rightarrow> bool" is "op <" .
lift_definition inf_nres_fun ::"('a, 'b) nres_fun \<Rightarrow> ('a, 'b) nres_fun \<Rightarrow> ('a, 'b) nres_fun" is inf
  unfolding nres_fun_separated_iff
 by force
lift_definition sup_nres_fun ::"('a, 'b) nres_fun \<Rightarrow> ('a, 'b) nres_fun \<Rightarrow> ('a, 'b) nres_fun" is sup
  unfolding nres_fun_separated_iff 
  apply auto
  apply (erule sup_nres.elims)
  subgoal by metis
  subgoal by metis
  subgoal by auto
  done

lift_definition top_nres_fun ::"('a, 'b) nres_fun" is top
  unfolding nres_fun_separated_iff
  by auto

lift_definition bot_nres_fun ::"('a, 'b) nres_fun" is bot
  unfolding nres_fun_separated_iff by auto

lift_definition Inf_nres_fun ::"('a, 'b) nres_fun set \<Rightarrow> ('a, 'b) nres_fun" is Inf
  unfolding nres_fun_separated_iff by auto

lift_definition Sup_nres_fun ::"('a, 'b) nres_fun set \<Rightarrow> ('a, 'b) nres_fun" is Sup
  unfolding nres_fun_separated_iff  
  apply auto
  unfolding image_iff
  by (metis)
instance
  apply (intro_classes)
  unfolding less_eq_nres_fun_def less_nres_fun_def
  unfolding bot_nres_fun_def top_nres_fun_def
  unfolding inf_nres_fun_def sup_nres_fun_def
  unfolding Inf_nres_fun_def Sup_nres_fun_def
  subgoal by (simp add: less_fun_def)
  subgoal by simp
  subgoal using less_eq_nres_fun.rep_eq by auto
  subgoal by (simp add: Rep_nres_fun_inject)
  subgoal using inf_nres_fun.rep_eq inf_nres_fun_def less_eq_nres_fun.rep_eq by auto
  subgoal using inf_nres_fun.rep_eq inf_nres_fun_def less_eq_nres_fun.rep_eq by auto
  subgoal using inf_nres_fun.rep_eq inf_nres_fun_def less_eq_nres_fun.rep_eq by auto
  subgoal using less_eq_nres_fun.rep_eq sup_nres_fun.rep_eq sup_nres_fun_def by auto
  subgoal using less_eq_nres_fun.rep_eq sup_nres_fun.rep_eq sup_nres_fun_def by auto
  subgoal using less_eq_nres_fun.rep_eq sup_nres_fun.rep_eq sup_nres_fun_def by auto
  subgoal by (metis Inf_lower Inf_nres_fun.rep_eq Inf_nres_fun_def image_eqI less_eq_nres_fun.rep_eq less_eq_nres_fun_def)
  subgoal by (smt Inf_greatest Inf_nres_fun.rep_eq Inf_nres_fun_def image_iff less_eq_nres_fun.rep_eq less_eq_nres_fun_def map_fun_apply)
  subgoal by (metis Sup_nres_fun.rep_eq Sup_nres_fun_def Sup_upper image_eqI less_eq_nres_fun.rep_eq less_eq_nres_fun_def)
  subgoal by (smt Sup_le_iff Sup_nres_fun.rep_eq Sup_nres_fun_def image_iff less_eq_nres_fun.rep_eq less_eq_nres_fun_def)
  subgoal by simp
  subgoal by simp
  done
end


datatype ('M, 'a) stateT = StateT (runStateT: "('M, 'a \<times> 'M) nres_fun")

instantiation stateT :: (type, type) complete_lattice
begin

fun less_eq_stateT where
  "StateT (f0) \<le> StateT (f1) \<longleftrightarrow> f0 \<le> f1"

fun less_stateT where
  "StateT (f0) < StateT (f1) \<longleftrightarrow> f0 < f1"

fun sup_stateT where
  "sup (StateT f0) (StateT f1) = StateT (sup f0 f1)"

fun inf_stateT where
  "inf (StateT f0) (StateT f1) = StateT (inf f0 f1)"

definition "Sup ts \<equiv> StateT (Sup (runStateT ` ts))"
definition "Inf ts \<equiv> StateT (Inf (runStateT ` ts))"

definition "bot \<equiv> StateT bot"
definition "top \<equiv> StateT top"

instance
  apply (intro_classes)
  unfolding Sup_stateT_def Inf_stateT_def bot_stateT_def top_stateT_def
  subgoal for x y by (cases x; cases y; auto)
  subgoal for x by (cases x; auto)
  subgoal for x y z by (cases x; cases y; cases z; auto)
  subgoal for x y by (cases x; cases y; auto)
  subgoal for x y by (cases x; cases y; auto)
  subgoal for x y by (cases x; cases y; auto)
  subgoal for x y z by (cases x; cases y; cases z; auto)
  subgoal for x y by (cases x; cases y; auto)
  subgoal for x y by (cases x; cases y; auto)
  subgoal for x y z by (cases x; cases y; cases z; auto)
  subgoal for x A by (cases x; force intro: Inf_lower)
  subgoal premises prems for A z by (cases z; force intro: Inf_greatest dest!: prems elim!: less_eq_stateT.elims)
  subgoal for x A by (cases x; force intro: Sup_upper)
  subgoal premises prems for A z by (cases z; force intro: Sup_least dest!: prems elim!: less_eq_stateT.elims)
  subgoal by auto
  subgoal by auto
  done
end    

definition returnT :: "'a \<Rightarrow> ('M, 'a) stateT" where
  "returnT a \<equiv> StateT (Abs_nres_fun (\<lambda>M. RETURN (a, M)))"

definition bindT :: "('M, 'a) stateT \<Rightarrow> ('a \<Rightarrow> ('M, 'b) stateT) \<Rightarrow> ('M, 'b) stateT" where
  "bindT s f \<equiv> StateT (Abs_nres_fun (\<lambda>M. do {
    (*nres monad*)
    (v, M') \<leftarrow> Rep_nres_fun (runStateT s) M;
    Rep_nres_fun (runStateT (f v)) M'
  }))"

adhoc_overloading
  Monad_Syntax.bind bindT

definition getT :: "('M, 'M) stateT" where
  "getT \<equiv> StateT (Abs_nres_fun (\<lambda>M. RETURN (M, M)))"

definition putT :: "'M \<Rightarrow> ('M, unit) stateT" where
  "putT M \<equiv> StateT (Abs_nres_fun (\<lambda>_. RETURN ((), M)))"

definition liftT :: "'a nres \<Rightarrow> ('M, 'a) stateT" where
  "liftT nr = StateT (Abs_nres_fun (\<lambda>M. do {
    (*nres monad*)
    v \<leftarrow> nr;
    RETURN (v, M)
  }))"

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
  "unpack_body body \<equiv> \<lambda>f (n, M). Rep_nres_fun (runStateT (body
    (\<lambda>a. StateT (Abs_nres_fun (\<lambda>M. f (a, M))))
  n)) M"

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

lemma mem_isvalid_update:
  assumes "mem_isvalid M" "v = Some (fib n)"
  shows "mem_isvalid (list_update M n v)"
  using assms unfolding mem_isvalid_def
  by (fastforce intro: cmem_intro simp: nth_list_update' elim: cmem_elim split: if_splits)

lemma mem_param_isvalid_elim:
  assumes "mem_isvalid M" "param_isvalid n"
  obtains "n < length M \<and> M!n = Some (fib n)" | "n < length M \<and> M!n = None"
  using assms unfolding mem_isvalid_def param_isvalid_def by (fastforce elim: cmem_elim)

definition fib_mem_spec :: "(nat \<times> tab) \<Rightarrow> (int \<times> tab) nres" where
  "fib_mem_spec \<equiv> \<lambda>(n, M). SPEC (\<lambda>(v, M'). fib n = v \<and> length M' = N+1 \<and> cmem M')"

definition crel_nt :: "('a nres \<Rightarrow> 'b nres \<Rightarrow> bool) \<Rightarrow> 'a nres \<Rightarrow> (tab, 'b) stateT \<Rightarrow> bool" where
  "crel_nt R nv t \<equiv>
    \<forall>M. mem_isvalid M \<longrightarrow>
      R nv (do {(v, M') \<leftarrow> runStateT t M; ASSERT (mem_isvalid M'); RETURN v})"

lemma crel_nt_intro:
  fixes nv t
  assumes "\<And>M. mem_isvalid M \<Longrightarrow> R nv (do {(v, M') \<leftarrow> runStateT t M; ASSERT (mem_isvalid M'); RETURN v})"
  shows "crel_nt R nv t"
  unfolding crel_nt_def using assms by auto

lemma crel_nt_dest:
  assumes "crel_nt R nv t" "mem_isvalid M"
  shows "R nv (do {(v, M') \<leftarrow> runStateT t M; ASSERT (mem_isvalid M'); RETURN v})"
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
  assumes "\<And>M. mem_isvalid M \<Longrightarrow> crel_nt R nr (tf M)"
  shows "crel_nt R nr (getT \<bind> tf)"
  using assms by (fastforce simp: getT_def bindT_def intro: crel_nt_intro dest: crel_nt_dest)

lemma crel_nt_putT:
  assumes "crel_nt R nr t" "mem_isvalid M"
  shows "crel_nt R nr (putT M \<then> t)"
  using assms by (fastforce simp: putT_def bindT_def intro: crel_nt_intro dest: crel_nt_dest)

lemma crel_nt_liftT:
  assumes "R nr0 nr1"
  shows "crel_nt R nr0 (liftT nr1)"
  using assms by (fastforce simp: liftT_def intro: crel_nt_intro)

lemma mem_isvalid_nres:
  assumes "mem_isvalid M" "param_isvalid n"
  shows "mop_list_get M n \<le> SPEC (\<lambda>v. v=None \<or> v=Some (fib n))"
  using assms by (refine_vcg) (auto elim: mem_param_isvalid_elim)

lemma crel_nt_bind_pure:
  assumes "crel_nt greater_eq (SPEC \<Phi>) t" "\<And>v. \<Phi> v \<Longrightarrow> crel_nt greater_eq nr (tf v)"
  shows "crel_nt greater_eq nr (t \<bind> tf)"
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
  assumes "param_isvalid n \<Longrightarrow> crel_nt greater_eq (RETURN (fib n)) t"
  shows "crel_nt greater_eq(fib_spec_at n) t"
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
  assumes "crel_nt greater_eq (fib_spec_at n) t" "param_isvalid n"
  shows "crel_nt greater_eq (RETURN (fib n)) t"
  apply (rule crel_nt_intro)
  apply (frule crel_nt_dest[OF assms(1)])
  unfolding fib_spec_at_def
  unfolding le_ASSERT_iff
  using assms(2) apply auto
  done

lemma crel_nt_returnT:
  "crel_nt greater_eq (RETURN v) (returnT v)"
  unfolding returnT_def by (fastforce intro: crel_nt_intro)

lemma crel_nt_checkmemT:
  assumes "crel_nt greater_eq (fib_spec_at n) t"
  shows "crel_nt greater_eq (fib_spec_at n) (checkmemT n t)"
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

lemma "runStateT (RECT body n) M = RECT (unpack_body body) (n, M)"
  oops

lemma "trimono body \<longleftrightarrow> trimono (unpack_body body)"
  apply (intro iffI)
  subgoal premises prems
    apply (unfold unpack_body_def comp_def)
    apply (rule trimonoI)
     apply (unfold monotone_def mono_def)
     apply auto
    thm trimonoD[OF prems]
    oops

definition crel_vt :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (tab, 'b) stateT \<Rightarrow> bool" where
  "crel_vt R v t \<equiv> \<forall>M. mem_isvalid M \<longrightarrow>
    do {(v', M') \<leftarrow> runStateT t M; ASSERT (mem_isvalid M'); RETURN (R v v')} \<le> RETURN True"

lemma crel_vt_intro:
  assumes "\<And>M. mem_isvalid M \<Longrightarrow>
    runStateT t M \<le> SPEC (\<lambda>(v', M'). R v v' \<and> mem_isvalid M')"
  shows "crel_vt R v t"
  unfolding crel_vt_def
  apply (intro allI impI)
  unfolding RETURN_SPEC_conv
  unfolding bind_rule_complete
  unfolding case_prod_bind_simp
  unfolding assert_bind_spec_conv
  unfolding SPEC_eq_is_RETURN
  unfolding nres_order_simps
  unfolding eq_True
  apply (subst conj_commute)
  apply (fact assms)
  done

lemma crel_vt_dest:
  assumes "crel_vt R v t" "mem_isvalid M"
  shows "runStateT t M \<le> SPEC (\<lambda>(v', M'). R v v' \<and> mem_isvalid M')"
  apply (insert assms)
  unfolding crel_vt_def
  apply (erule allE impE)+
   apply (assumption)
  unfolding RETURN_SPEC_conv
  unfolding bind_rule_complete
  unfolding case_prod_bind_simp
  unfolding assert_bind_spec_conv
  unfolding SPEC_eq_is_RETURN
  unfolding nres_order_simps
  unfolding eq_True
  apply (erule order_trans)
  apply (rule SPEC_rule)
  apply clarify
  done

lemma crel_vt_getT:
  assumes "\<And>M. mem_isvalid M \<Longrightarrow> crel_vt R v (tf M)"
  shows "crel_vt R v (getT \<bind> tf)"
  apply (rule crel_vt_intro)
  unfolding getT_def
  unfolding bindT_def
  unfolding stateT.sel
  unfolding nres_monad1
  unfolding prod.case
  apply (frule assms)
  apply (drule crel_vt_dest)
   apply assumption+
  done

lemma crel_vt_putT:
  assumes "crel_vt R v t" "mem_isvalid M"
  shows "crel_vt R v (putT M \<then> t)"
  apply (rule crel_vt_intro)
  unfolding putT_def
  unfolding bindT_def
  unfolding stateT.sel
  unfolding nres_monad1
  unfolding prod.case
  apply (rule crel_vt_dest[OF assms])
  done

lemma crel_vt_bindT:
  assumes "crel_vt (op =) v t" "crel_vt R (f v) (tf v)"
  shows "crel_vt R (f v) (t \<bind> tf)"
  apply (rule crel_vt_intro)
  unfolding bindT_def
  unfolding stateT.sel
  unfolding bind_rule_complete
  unfolding case_prod_bind_simp
  apply (drule crel_vt_dest[OF assms(1)])
  apply (erule order_trans)
  apply (rule SPEC_rule)
  apply clarify
  apply (drule crel_vt_dest[OF assms(2)])
  apply assumption
  done

lemma mop_list_aux:
  assumes "mem_isvalid M" "param_isvalid n"
  shows "mop_list_get M n = RETURN (M!n)"
    "mop_list_set M n (Some (fib n)) = RETURN (list_update M n (Some (fib n)))"
    "mop_list_set M n None = RETURN (list_update M n None)"
  using assms by (auto elim: mem_param_isvalid_elim)

lemma crel_vt_liftT:
  assumes "nr \<le> RETURN v"
  shows "crel_vt (op =) v (liftT nr)"
  apply (rule crel_vt_intro)
  unfolding liftT_def
  unfolding stateT.sel
  unfolding bind_rule_complete
  apply (rule assms[THEN order_trans])
  unfolding RETURN_SPEC_conv
  apply (rule SPEC_rule)
  apply (rule SPEC_rule)
  apply clarify
  done

lemma crel_vt_returnT:
  assumes "R v v'"
  shows "crel_vt R v (returnT v')"
  apply (rule crel_vt_intro)
  unfolding returnT_def
  unfolding stateT.sel
  apply (rule RETURN_rule)
  apply clarify
  apply (rule assms)
  done

lemma crel_vt_checkmemT:
  assumes "crel_vt (op =) (fib n) t" "param_isvalid n"
  shows "crel_vt (op =) (fib n) (checkmemT n t)"
  unfolding checkmemT_def
  apply (rule crel_vt_getT)
  apply (rule crel_vt_bindT)
  apply (rule crel_vt_liftT)
  unfolding mop_list_aux[OF _ assms(2)]
  apply (rule plain_RETURN)
  apply (split option.split)
  apply (intro conjI; intro impI allI)
  subgoal
    apply (rule crel_vt_bindT)
     apply (rule assms(1))
    apply (rule crel_vt_bindT)
     apply (rule crel_vt_liftT)
    unfolding mop_list_aux[OF _ assms(2)]
     apply (rule plain_RETURN)
    apply (rule crel_vt_putT)
     apply (rule crel_vt_returnT)
     apply (rule refl)
    apply (rule mem_isvalid_update)
     apply assumption
    apply (rule refl)
    done
  subgoal
    apply (rule crel_vt_returnT)
    using assms(2) by (fastforce elim: mem_param_isvalid_elim)
  done

lemma flat_ge_stateT:
  "flat_ge (StateT t0) (StateT t1) \<Longrightarrow> flatf_ge t0 t1"
  apply (rule fun_ordI)
  apply (rule flat_ordI)
  unfolding flat_ord_def
  unfolding top_stateT_def
  by auto

lemma
  assumes "trimono bodyT"
  shows "trimono (unpack_body bodyT)"
  apply (rule trimonoI)
    defer
  subgoal
    apply (rule monoI)
    unfolding unpack_body_def
    apply (rule le_funI)
    apply (split prod.splits)
    apply clarify
    apply (rule le_funD) back
    unfolding less_eq_stateT.simps[symmetric]
    unfolding stateT.collapse
    apply (rule le_funD) back
    apply (rule trimonoD_mono[OF assms, THEN monoD])
    unfolding comp_def
    apply (rule le_funI)
    unfolding less_eq_stateT.simps
    unfolding curry_def
    apply (rule le_funI)
    apply (drule le_funD)
    apply assumption
    done
  subgoal
    apply (rule monotoneI)
    apply (rule fun_ordI)
    unfolding unpack_body_def
    apply (split prod.splits)
    apply clarify
    apply (rule fun_ordD[of flat_ge]) back
    apply (rule flat_ge_stateT)
    unfolding stateT.collapse
    apply (rule fun_ordD[of flat_ge]) back
    apply (rule trimonoD_flatf_ge[OF assms, THEN monotoneD])
    unfolding comp_def
    apply (rule fun_ordI)
    apply (rule flat_ordI)
    unfolding curry_def top_stateT_def
    unfolding stateT.inject
    apply (rule ext)
    apply (drule fun_ordD[of "flat_ord FAIL"])
    unfolding flat_ord_def
    apply (erule disjE)
     defer
    apply assumption
    apply simp
  oops
  thm le_fun_def
  term comp
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
