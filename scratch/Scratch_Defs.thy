theory Scratch_Defs
  imports Refine_Imperative_HOL.IICF
begin
      
typ assn
typ "'a array"
lemma "id_assn \<equiv> pure Id" .
lemma "array_assn A \<equiv> hr_comp is_array (\<langle>the_pure A\<rangle>list_rel)" unfolding array_assn_def .
lemma "\<langle>x\<rangle>f \<equiv> relAPP f x" .
lemma "\<langle>x, y\<rangle>f \<equiv> relAPP (relAPP f x) y" .
lemma "relAPP f x \<equiv> f x" unfolding relAPP_def .
lemma "the_pure P \<equiv> THE P'. \<forall>x x'. P x x'=\<up>((x',x)\<in>P')" unfolding the_pure_def .
lemma "is_array l p \<equiv> p\<mapsto>\<^sub>al" unfolding is_array_def .
lemma "r\<mapsto>\<^sub>aa = Abs_assn (\<lambda>(h,as). Array.get h r = a \<and> as = {addr_of_array r} \<and> addr_of_array r < lim h)" unfolding snga_assn_def by (rule cong[of Abs_assn]) auto
lemma "pure R \<equiv> (\<lambda>a c. \<up>((c,a)\<in>R))" unfolding pure_def .
lemma "is_pure P \<equiv> \<exists>P'. \<forall>x x'. P x x'=\<up>(P' x x')" unfolding is_pure_def .
lemma "\<up>b = Abs_assn (\<lambda>(h, as). as={} \<and> b)" unfolding pure_assn_def by (rule cong[of Abs_assn]) auto
lemma "R\<^sup>k = (R, R)" by simp
lemma "R\<^sup>d = (R,invalid_assn R)" by simp
lemma "RS \<rightarrow>\<^sub>a T \<equiv> ([\<lambda>_. True]\<^sub>a RS \<rightarrow> T)" .
lemma "[P]\<^sub>a RS \<rightarrow> T \<equiv> { (f,g) . \<forall>c a.  P a \<longrightarrow> hn_refine (fst RS a c) (f c) (snd RS a c) T (g a)}" unfolding hfref_def .
lemma "hn_refine \<Gamma> c \<Gamma>' R m \<equiv> nofail m \<longrightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up>(RETURN x \<le> m)) >\<^sub>t" unfolding hn_refine_def .
lemma "nofail S \<equiv> S\<noteq>FAIL" unfolding nofail_def .
lemma "invalid_assn R \<equiv> \<lambda>x y. \<up>(\<exists>h. h\<Turnstile>R x y) * true" unfolding invalid_assn_def .
lemma "P * Q = Abs_assn (\<lambda>(h,as). \<exists>as1 as2. as=as1\<union>as2 \<and> as1\<inter>as2={} \<and> Rep_assn P (h,as1) \<and> Rep_assn Q (h,as2))" unfolding times_assn_def by (rule cong[of Abs_assn]) (auto split: prod.splits)
lemma "true = Abs_assn (\<lambda>(h,as). (\<forall>a\<in>as. a < lim h))" unfolding top_assn_def by (rule cong[of Abs_assn]) (auto simp: in_range.simps)
lemma "false = Abs_assn (\<lambda>_. False)" unfolding bot_assn_def ..
lemma "in_range (h,as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)" unfolding in_range.simps ..
lemma "emp = Abs_assn (\<lambda>(h,as). as={})"  unfolding one_assn_def by (rule cong[of Abs_assn]) auto
thm "HOL_list.fold_custom_empty"
find_theorems  list_custom_empty
term arl_empty
term heap_array_empty
thm list_custom_empty.fold_custom_empty
lemma "h\<Turnstile>P \<equiv> Rep_assn P h" .

lemma "vassn_tag \<Gamma> \<equiv> \<exists>h. h\<Turnstile>\<Gamma>" unfolding vassn_tag_def .
lemma "hn_val R \<equiv> hn_ctxt (pure R)" .
lemma "hn_ctxt P a c \<equiv> P a c" unfolding Sepref_Basic.hn_ctxt_def .
lemma "op_array_of_list \<equiv> op_list_copy" by simp
lemma "op_list_copy l \<equiv> l" by simp

thm sepref_fr_rules
find_theorems hn_refine op_array_of_list

lemma True
  -- \<open>The preprocessing phase converts the goal into 
    the @{const "hn_refine"}-form. Moreover, it adds interface type 
    annotations for the parameters. (for now, the interface type is just the HOL 
    type of the parameter, in our case, @{typ "nat list"})\<close>
  apply sepref_dbg_preproc
  -- \<open>The next phase applies a consequence rule for the postcondition and
    result. This is mainly for technical reasons.\<close>
  apply sepref_dbg_cons_init
  -- \<open>The next phase tries to identify the abstract operations, and inserts
    tag-constants for function application and abstraction. These tags are for 
    technical reasons, working around Isabelle/HOL's unifier idiosyncrasies.

    Operation identification assigns a single constant to each abstract operation,
    which is required for technical reasons. Note that there are terms in HOL, 
    which qualify as a single operation, but consists of multiple constants, 
    for example, @{term "{x}"}, which is just syntactic sugar for 
    @{term [source] "insert x {}"}. In our case, the operation identification 
    phase rewrites the assertion operations followed by a bind to a single 
    operation @{const op_ASSERT_bind}, and renames some operations to more 
    canonical names.
    \<close>
  apply sepref_dbg_id
  -- \<open>Now that it is clear which operations to execute, we have to specify an 
    execution order. Note that HOL has no notion of execution at all. However,
    if we want to translate to operations that depend on a heap, we need a notion 
    of execution order. We use the \<open>nres\<close>-monad's bind operation as sequencing operator,
    and flatten all nested operations, using left-to-right evaluation order. 
    \<close>
  apply sepref_dbg_monadify
  -- \<open>The next step just prepares the optimization phase,
    which will be executed on the translated program. It just applies the rule   
    @{thm TRANS_init}.\<close>
  apply sepref_dbg_opt_init
  -- \<open>The translation phase does the main job of translating the abstract program
    to the concrete one. It has rules how to translate abstract operations to
    concrete ones. For technical reasons, it differentiates between 
    operations, which have only first-order arguments (e.g., @{const length})   
    and combinators, which have also higher-order arguments (e.g., @{const fold}).

    The basic idea of translation is to repeatedly apply the translation rule for the
    topmost combinator/operator, and thus recursively translate the whole program.
    The rules may produce various types of side-conditions, which are resolved by the tool.
    \<close>
  apply sepref_dbg_trans
  -- \<open>The next phase applies some simplification rules to optimize the translated program.
    It essentially simplifies first with the rules @{thm [source] sepref_opt_simps}, and
    then with @{thm [source] sepref_opt_simps2}.
    \<close>
  apply sepref_dbg_opt
  -- \<open>The next two phases resolve the consequence rules introduced by the \<open>cons_init\<close> phase.\<close>
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  -- \<open>The translation phase and the consequence rule solvers may postpone some
    side conditions on yet-unknown refinement assertions. These are solved in the 
    last phase.\<close>
  apply sepref_dbg_constraints
  oops

lemma "ASSERT \<equiv> iASSERT RETURN" unfolding ASSERT_def .
lemma "iASSERT returnf \<Phi> \<equiv> if \<Phi> then returnf () else top" unfolding iASSERT_def .
lemma "Refine_Basic.bind M f \<equiv> case M of 
  FAILi \<Rightarrow> FAIL |
  RES X \<Rightarrow> Sup (f`X)"
  unfolding Refine_Basic.bind_def .
lemma "top::'a nres \<equiv> FAILi" unfolding Refine_Basic.top_nres_def .
lemma "bot::'a nres \<equiv> RES {}" unfolding Refine_Basic.bot_nres_def .

term op_list_get
term op_list_set
find_theorems op_list_set term 0
thm HOL_list.fold_custom_empty
term list_custom_empty

term flatf_gfp
term flatf_ord.fixp
term trimono
