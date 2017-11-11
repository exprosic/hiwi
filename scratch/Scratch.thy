theory Scratch
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
lemma "\<up>b \<equiv> Abs_assn (pure_assn_raw b)" unfolding pure_assn_def .
lemma "pure_assn_raw b (h,as) \<longleftrightarrow> as={} \<and> b" by simp
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