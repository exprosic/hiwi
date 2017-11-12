theory Scratch_Fib
  imports Refine_Imperative_HOL.IICF
begin

fun fib :: "nat \<Rightarrow> int" where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib (Suc n) + fib n"

definition fib_spec :: "nat \<Rightarrow> int nres" where
  "fib_spec n \<equiv> RETURN (fib n)"

term RECT
term REC
term trimono

definition fib_rec_body :: "(nat \<Rightarrow> int nres) \<Rightarrow> nat \<Rightarrow> int nres" where
  "fib_rec_body \<equiv> \<lambda>f n.
    if n < 2
      then RETURN 1
      else do {
        f0 \<leftarrow> f (n-2);
        f1 \<leftarrow> f (n-1);
        RETURN (f0+f1)
      }"

definition fib_rec_body' :: "(nat \<Rightarrow> int nres) \<Rightarrow> nat \<Rightarrow> int nres" where
  "fib_rec_body \<equiv> \<lambda>f n.
    case n of
      0 \<Rightarrow> RETURN 1
    | Suc 0 \<Rightarrow> RETURN 1
    | Suc (Suc n') \<Rightarrow> do {
        f0 \<leftarrow> f n';
        f1 \<leftarrow> f (Suc n');
        RETURN (f0+f1)
      }"
definition fib_rec :: "nat \<Rightarrow> int nres" where
  "fib_rec n \<equiv> RECT fib_rec_body n"

lemma fib_rec_refine: "(fib_rec, fib_spec) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding fib_rec_def fib_spec_def
  apply (clarsimp intro!: nres_relI simp:)
  apply (refine_vcg RECT_rule[where body=fib_rec_body and V=less_than and pre="\<lambda>_. True" and M="\<lambda>n. RETURN (fib n)"])
  subgoal unfolding fib_rec_body_def by refine_mono
  subgoal ..
  subgoal ..
  subgoal premises prems for _ f n
    thm prems(1)[simplified] prems(3)[symmetric]
    unfolding fib_rec_body_def
    apply (refine_vcg order_trans[OF prems(1)]; cases n rule: fib.cases; simp)
done

    term 0 (*
    subgoal premises prems'[simp] for m
      thm prems(1)[of m, simplified] prems(1)[of "Suc m", simplified]
      apply (rule order_trans)
       apply (rule prems(1)[of m, simplified])
      apply simp
      unfolding RETURN_def[symmetric]
      apply (refine_vcg)
      apply (rule order_trans)
       apply (rule prems(1)[of "Suc m", simplified])
      apply simp
      done
    done
  done
term 0 (*
sepref_definition fib_rec1 is fib_rec :: "nat_assn\<^sup>d \<rightarrow>\<^sub>a int_assn"
  unfolding fib_rec_def fib_rec_body_def
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
        apply sepref_dbg_trans_step_keep
















