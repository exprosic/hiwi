theory Monad
  imports Main
begin

datatype ('M, 'a) state = State (runState: "'M \<Rightarrow> 'a \<times> 'M")
term 0 (**)

definition return :: "'a \<Rightarrow> ('M, 'a) state" where
  "return a \<equiv> State (\<lambda>M. (a, M))"
term 0 (**)

definition bind :: "('M, 'a) state \<Rightarrow> ('a \<Rightarrow> ('M, 'b) state) \<Rightarrow> ('M, 'b) state" (infixl "\<bind>" 54) where
  "s \<bind> k \<equiv> State (\<lambda>M. let (a, M') = runState s M in runState (k a) M')"
term 0 (**)
  
abbreviation then_monad :: "('M, 'a) state \<Rightarrow> ('M, 'b) state \<Rightarrow> ('M, 'b) state" (infixl "\<then>" 54) where
  "s \<then> s' \<equiv> s \<bind> (\<lambda>_. s')"
term 0 (**)

definition get :: "('M, 'M) state" where
  "get \<equiv> State (\<lambda>M. (M, M))"

definition put :: "'M \<Rightarrow> ('M, unit) state" where
  "put M \<equiv> State (\<lambda>_. ((), M))"
term 0 (**)
  
nonterminal exec_binds and exec_bind
syntax
  "_exec_block" :: "exec_binds \<Rightarrow> 'a" ("exec {//(2  _)//}" [12] 62)
  "_exec_bind"  :: "[pttrn, 'a] \<Rightarrow> exec_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_exec_let" :: "[pttrn, 'a] \<Rightarrow> exec_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_exec_then" :: "'a \<Rightarrow> exec_bind" ("_" [14] 13)
  "_exec_final" :: "'a \<Rightarrow> exec_binds" ("_")
  "_exec_cons" :: "[exec_bind, exec_binds] \<Rightarrow> exec_binds" ("_;//_" [13, 12] 12)

translations
  "_exec_block (_exec_cons (_exec_then t) (_exec_final e))"
    \<rightleftharpoons> "CONST then_monad t e"
  "_exec_block (_exec_cons (_exec_bind p t) (_exec_final e))"
    \<rightleftharpoons> "CONST bind t (\<lambda>p. e)"
  "_exec_block (_exec_cons (_exec_let p t) bs)"
    \<rightleftharpoons> "let p = t in _exec_block bs"
  "_exec_block (_exec_cons b (_exec_cons c cs))"
    \<rightleftharpoons> "_exec_block (_exec_cons b (_exec_final (_exec_block (_exec_cons c cs))))"
  "_exec_cons (_exec_let p t) (_exec_final s)"
    \<rightleftharpoons> "_exec_final (let p = t in s)"
  "_exec_block (_exec_final e)" \<rightharpoonup> "e"

term 0 (**)
lemma bind_assoc:
  "(s \<bind> k0) \<bind> k1 = s \<bind> (\<lambda>a. k0 a \<bind> k1)"
  unfolding bind_def by (auto split: prod.split)

lemma left_identity:
  "return v \<bind> k = k v"
  unfolding return_def bind_def by simp

lemma right_identity:
  "s \<bind> return = s"
  unfolding return_def bind_def by simp

lemma runState_return:
  "runState (return x) M = (x, M)"
  unfolding return_def by simp
end