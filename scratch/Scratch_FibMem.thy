theory Scratch_FibMem
  imports Refine_Imperative_HOL.IICF "dp/Monad"
begin

fun fib :: "nat \<Rightarrow> int" where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib (Suc n) + fib n"

type_synonym tab = "int list"

(*Since fib n \<ge> 0, negative value is used here to represent None*)
definition is_some :: "int \<Rightarrow> bool" where
  "is_some v \<equiv> v \<ge> 0"

definition checkmem :: "tab \<Rightarrow> nat \<Rightarrow> (tab \<times> int) nres \<Rightarrow> (tab \<times> int) nres" where
  "checkmem M n v \<equiv> do {
    fn \<leftarrow> mop_list_get M n;
    if is_some fn
      then RETURN (M, fn)
      else do {
        (M, fn) \<leftarrow> v;
        M \<leftarrow> mop_list_set M n fn;
        RETURN (M, fn)
      }
    }"

definition fib_rec_mem_body :: "((tab \<times> nat) \<Rightarrow> (tab \<times> int) nres) \<Rightarrow> (tab \<times> nat) \<Rightarrow> (tab \<times> int) nres" where
  "fib_rec_mem_body \<equiv> \<lambda>f (M, n). checkmem M n (do {
    if n < 2
      then RETURN (M, 1)
      else do {
        (M, f0) \<leftarrow> f (M, n-2);
        (M, f1) \<leftarrow> f (M, n-1);
        RETURN (M, f0 + f1)
      }
    })"

definition fib_rec_mem :: "nat \<Rightarrow> int nres" where
  "fib_rec_mem n \<equiv> do {
    (_, v) \<leftarrow> RECT fib_rec_mem_body (replicate (n+1) (-1), n);
    RETURN v
   }"

sepref_definition fib_rec_mem1 is fib_rec_mem :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a int_assn"
  unfolding fib_rec_mem_def fib_rec_mem_body_def checkmem_def is_some_def
  apply (rewrite in "RECT _ (\<hole>, _)" array_fold_custom_of_list)
  by sepref

definition fib_rec_mem_body' where
  "fib_rec_mem_body' \<equiv> \<lambda>f n. "

term 0 (*

definition cmem :: "tab \<Rightarrow> bool" where
  "cmem M \<equiv> \<forall>i. i<length M \<longrightarrow> M!i\<ge>0 \<longrightarrow> M!i=fib i"

lemma cmem_intro:
  assumes "\<And>i. i<length M \<Longrightarrow> M!i\<ge>0 \<Longrightarrow> M!i=fib i"
  shows "cmem M"
  using assms unfolding cmem_def by fastforce

lemma cmem_elim:
  assumes "cmem M" "i < length M"
  obtains "M!i < 0" | "fib i = M!i "
  using assms unfolding cmem_def by fastforce
  term 0 

lemma cmem_update:
  "\<lbrakk>cmem M; v = fib i\<rbrakk> \<Longrightarrow> cmem (list_update M i v)"
  by (fastforce intro!: cmem_intro elim: cmem_elim simp: nth_list_update')

definition crel_vs :: "'a nres \<Rightarrow> (tab \<times> 'a) nres \<Rightarrow> bool" where
  "crel_vs v s \<equiv> nofail v \<longrightarrow> the"

end